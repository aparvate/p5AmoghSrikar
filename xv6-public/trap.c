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
  case T_PGFLT: 
   uint trap_addr = rcr2();
   struct proc *p = myproc();
  
   int i = find_mapping_trap(trap_addr);

   if (i < 16) { // lazy allocation
       char *mem = kalloc();
       if(mem == 0) {
         p->killed = 1;
         break;
       }
       memset(mem, 0, PGSIZE);


       if(mappages(p->pgdir, (char*)PGROUNDDOWN(trap_addr), PGSIZE, V2P(mem), PTE_W|PTE_U) >= 0) {
         acquire(&CopyWriteLock);
         references[V2P(mem) / PGSIZE] = 1;
         release(&CopyWriteLock);
       }
       else{
         kfree(mem);
         p->killed = 1;
       }
      
       if(p->maps[i].fd != -1){
         uint offset = PGROUNDDOWN(trap_addr) - p->maps[i].addr;
         if(change_offset_then_fileread(p->maps[i].file, mem, PGSIZE, offset) < 0){
           p->killed = 1;
         }
       }


   } else {
       pte_t *pte;
       pte = walkpgdir(p->pgdir, (void *)PGROUNDDOWN(trap_addr), 0);
       uint flags = PTE_FLAGS(*pte);
       if((flags & PTE_U) && (flags & PTE_P) && (flags & PTE_COW)){
         char *mem = kalloc();
         if(mem == 0) {
           p->killed = 1;
           break;
         }
         uint pa = PTE_ADDR((*pte));
         memmove(mem, (char *)P2V(pa), PGSIZE);
         *pte = 0;
         if(mappages(p->pgdir, (char*)PGROUNDDOWN(trap_addr), PGSIZE, V2P(mem), PTE_W|PTE_U) >= 0) {
          acquire(&CopyWriteLock);
          references[pa / PGSIZE] --;
          references[V2P(mem) / PGSIZE] = 1;
          release(&CopyWriteLock);

         } else{
           kfree(mem);
           p->killed = 1;
         }
       }
       else{
         cprintf("Segmentation Fault\n");
         p->killed = 1;
       }
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

int
find_mapping_trap(uint trap_addr){
 int i;
 struct proc *p = myproc();
  // Find the mapping that contains this fault
 // add PGROUNDUP because we will always allocate entire page even when length is not a multiple of page size
 for(i = 0; i < 16; i++) {
   if((p->maps[i].flags & PTE_P) &&
       trap_addr >= p->maps[i].addr &&
       trap_addr < p->maps[i].addr + PGROUNDUP(p->maps[i].length))
    break;
 }
 return i;
}