#include "types.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "x86.h"
#include "proc.h"
#include "traps.h"
#include "spinlock.h"
#include <stdbool.h>
#include "wmap.h"
#include "sleeplock.h"
#include "fs.h"
#include "file.h"

// Interrupt descriptor table (shared by all CPUs).
struct gatedesc idt[256];
extern uint vectors[];  // in vectors.S: array of 256 entry pointers
struct spinlock tickslock;
uint ticks;

extern struct spinlock CopyWriteLock;
extern uchar references[PHYSTOP/PGSIZE];

void
tvinit(void)
{
  int i;

  for(i = 0; i < 256; i++)
    SETGATE(idt[i], 0, SEG_KCODE<<3, vectors[i], 0);
  SETGATE(idt[T_SYSCALL], 1, SEG_KCODE<<3, vectors[T_SYSCALL], DPL_USER);

  initlock(&tickslock, "time");
}

void
idtinit(void)
{
  lidt(idt, sizeof(idt));
}

//PAGEBREAK: 41
void
trap(struct trapframe *tf)
{
  if(tf->trapno == T_SYSCALL){
    if(myproc()->killed)
      exit();
    myproc()->tf = tf;
    syscall();
    if(myproc()->killed)
      exit();
    return;
  }

  switch(tf->trapno){
  case T_IRQ0 + IRQ_TIMER:
    if(cpuid() == 0){
      acquire(&tickslock);
      ticks++;
      wakeup(&ticks);
      release(&tickslock);
    }
    lapiceoi();
    break;
  case T_IRQ0 + IRQ_IDE:
    ideintr();
    lapiceoi();
    break;
  case T_IRQ0 + IRQ_IDE+1:
    // Bochs generates spurious IDE1 interrupts.
    break;
  case T_IRQ0 + IRQ_KBD:
    kbdintr();
    lapiceoi();
    break;
  case T_IRQ0 + IRQ_COM1:
    uartintr();
    lapiceoi();
    break;
  case T_IRQ0 + 7:
  case T_IRQ0 + IRQ_SPURIOUS:
    cprintf("cpu%d: spurious interrupt at %x:%x\n",
            cpuid(), tf->cs, tf->eip);
    lapiceoi();
    break;
  case T_PGFLT: // T_PGFLT = 14
    uint address_of_fault = rcr2();
    struct proc *p = myproc();
    struct map_wmap *map;
    int segFaultFound = 0;

    //cprintf("Trap handler - PID: %d\n", p->pid);

    // if page fault addr is part of a mapping: // lazy allocation
    // handle it
    int indexOfFault = 0;
    for (indexOfFault = 0; indexOfFault < 16; indexOfFault++) {
      //cprintf("Index in trap handler: %d\n", indexOfFault);
      map = &p->maps[indexOfFault];

      // Check if the faulting address lies within the current mapping's range
      if (address_of_fault >= map->addr && address_of_fault < (map->addr + map->length)) {
        segFaultFound = 1;
        break;
      }
    }
    //cprintf("Index of fault addr found: %d\n", indexOfFault);
    if (indexOfFault < 16) {
      //cprintf("Go into lazy handler\n");
      // Allocate a new physical page
      char *mem = kalloc();
      memset(mem, 0, PGSIZE);

      // Calculate the start of the page for mapping
      uint start_of_page = PGROUNDDOWN(address_of_fault);
      //cprintf("Page start calculated\n");

      // Handle file-backed mappings for MAP_SHARED
      if (map->file && (map->flags & MAP_SHARED)) {
        uint file_offset = start_of_page - map->addr; // Calculate file offset
        //cprintf("Filed offset calculated\n");

        // Read file data into the newly allocated page
        int bytes_read = readi(map->file->ip, mem, file_offset, PGSIZE);
        //cprintf("Bytes read\n");
        if (bytes_read < 0) {
          kfree(mem); // Free allocated memory on failure
          panic("trap: file read failed\n");
        }
        //cprintf("trap: file read succeeded\n");
      }

      // Map the allocated page into the process's page table
      p->pgdir = 0;
      //cprintf("Mappages result: %d", mappages(p->pgdir, (void *)start_of_page, PGSIZE, V2P(mem), PTE_W | PTE_U));
      if (mappages(p->pgdir, (void *)start_of_page, PGSIZE, V2P(mem), PTE_W | PTE_U) < 0) {
        kfree(mem); // Free allocated memory on failure
        panic("trap: page mapping failed\n");
      }
      else{
        //cprintf("trap: page mapping succeded\n");
        acquire(&CopyWriteLock);
        //cprintf("CopyWriteLock acquired in trap handler\n");
        uint mem_index = V2P(mem)/PGSIZE;
        if (references[mem_index] != 0){
          references[mem_index] = references[mem_index] + 1;
        }
        else{
          references[mem_index] = 1;
        }
        //cprintf("References decremented\n");
        release(&CopyWriteLock);
        //cprintf("Lock released\n");
      }
    }
    else {
      //cprintf("Past 15, 16 or above, non-lazy\n");
      pte_t *pte;
      pte = walkpgdir(p->pgdir, (void *)PGROUNDDOWN(address_of_fault), 0);
      uint flags = PTE_FLAGS(*pte);
      //cprintf("Check if user, present (always there) and then cow\n");
      if((flags & PTE_U) && (flags & PTE_P) && (flags & PTE_COW)){
        //cprintf("Try allocation\n");
        char *mem = kalloc();
        if(mem == 0) {
          p->killed = 1;
          break;
        }
        //cprintf("Alloc succeeded\n");
        uint pa = PTE_ADDR((*pte));
        //cprintf("Write to address\n");
        memmove(mem, (char *)P2V(pa), PGSIZE);
        *pte = 0;
        //cprintf("Check if paged\n");
        if(mappages(p->pgdir, (char*)PGROUNDDOWN(address_of_fault), PGSIZE, V2P(mem), PTE_W|PTE_U) >= 0) {
          acquire(&CopyWriteLock);
          //cprintf("Lock in trap handler past 16 acquired\n");
          references[pa / PGSIZE] --;
          references[V2P(mem) / PGSIZE] = 1;
          release(&CopyWriteLock);
          //cprintf("Lock in trap handler past 16 released\n");
          segFaultFound = 1;

        } else{
          kfree(mem);
          p->killed = 1;
        }
      }
      else{
        //cprintf("This means that it either wasn't present, useable, or COW\n");
        cprintf("Segmentation Fault\n");
        //cprintf("Within the Else Statement\n");
        p->killed = 1;
      }
    }

      
    if(segFaultFound == 0) {
      cprintf("Segmentation Fault\n");
      //cprintf("Without the Else statement\n");
      // kill the process
      p->killed = 1;
    }
    break;

  //PAGEBREAK: 13
  default:
    if(myproc() == 0 || (tf->cs&3) == 0){
      // In kernel, it must be our mistake.
      cprintf("unexpected trap %d from cpu %d eip %x (cr2=0x%x)\n",
              tf->trapno, cpuid(), tf->eip, rcr2());
      panic("trap");
    }
    // In user space, assume process misbehaved.
    cprintf("pid %d %s: trap %d err %d on cpu %d "
            "eip 0x%x addr 0x%x--kill proc\n",
            myproc()->pid, myproc()->name, tf->trapno,
            tf->err, cpuid(), tf->eip, rcr2());
    myproc()->killed = 1;
  }

  // Force process exit if it has been killed and is in user space.
  // (If it is still executing in the kernel, let it keep running
  // until it gets to the regular system call return.)
  if(myproc() && myproc()->killed && (tf->cs&3) == DPL_USER)
    exit();

  // Force process to give up CPU on clock tick.
  // If interrupts were on while locks held, would need to check nlock.
  if(myproc() && myproc()->state == RUNNING &&
     tf->trapno == T_IRQ0+IRQ_TIMER)
    yield();

  // Check if the process has been killed since we yielded
  if(myproc() && myproc()->killed && (tf->cs&3) == DPL_USER)
    exit();
}
