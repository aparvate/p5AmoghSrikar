#include "types.h"
#include "defs.h"
#include "param.h"
#include "spinlock.h"
#include "sleeplock.h"
#include "fs.h"
#include "file.h"
#include "memlayout.h"
#include "mmu.h"
#include "proc.h"
#include "x86.h"
#include "traps.h"

// Interrupt descriptor table (shared by all CPUs).
struct gatedesc idt[256];
extern uint vectors[];  // in vectors.S: array of 256 entry pointers
struct spinlock tickslock;
uint ticks;

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

// Helper Functions
// Handle lazy allocation and memory mapping
int handle_page_fault(struct proc *curproc, uint fault_addr, uint page_addr) {
    if (is_valid_user_address(fault_addr)) {
        for (int i = 0; i < curproc->wmapinfo.total_mmaps; i++) {
            if (is_fault_in_mapped_range(curproc, fault_addr, i)) {
                return handle_memory_mapping(curproc, fault_addr, page_addr, i);
            }
        }
    }
    return handle_cow_or_invalid_page(curproc, fault_addr, page_addr);
}

// Check if the fault address is within a valid user space range
int is_valid_user_address(uint addr) {
    return (addr % PGSIZE == 0) && (addr >= KERNSTART) && (addr < KERNBASE);
}

// Check if fault_addr falls within the mapped range of the given index
int is_fault_in_mapped_range(struct proc *curproc, uint fault_addr, int idx) {
    uint start = curproc->wmapinfo.addr[idx];
    uint end = start + curproc->wmapinfo.length[idx];
    return (fault_addr >= start && fault_addr < end);
}

// Handle memory-mapped files and anonymous mappings
int handle_memory_mapping(struct proc *curproc, uint fault_addr, uint page_addr, int idx) {
    char *mem = kalloc();
    if (!mem) {
        return 1; // Allocation failure
    }

    memset(mem, 0, PGSIZE);
    if (mappages(curproc->pgdir, (void *)page_addr, PGSIZE, V2P(mem), PTE_U | PTE_W) < 0) {
        kfree(mem);
        cprintf("mappages failed\n");
        return 1;
    }

    if (curproc->wmapinfo.fd[idx] >= 0 && !(curproc->wmapinfo.flags[idx] & MAP_ANONYMOUS)) {
        struct file *f = curproc->ofile[curproc->wmapinfo.fd[idx]];
        if (f) {
            ilock(((struct inode *)f->ip));
            readi(f->ip, (char *)page_addr, page_addr - curproc->wmapinfo.addr[idx], PGSIZE);
            iunlock(((struct inode *)f->ip));
        }
    }

    curproc->wmapinfo.n_loaded_pages[idx]++;
    return 2; // Success
}

// Handle copy-on-write or invalid pages
int handle_cow_or_invalid_page(struct proc *curproc, uint fault_addr, uint page_addr) {
    uint *pte = walkpgdir(curproc->pgdir, (void *)page_addr, 0);
    if (!pte || !(*pte & PTE_P) || !(*pte & PTE_U)) {
        return 1; // Invalid page
    }

    uint physical_addr = PTE_ADDR(*pte);

    if (*pte & PTE_COW) {
        return handle_cow_page(curproc, pte, physical_addr);
    } else if (!(*pte & PTE_W)) {
        *pte |= PTE_W;
        lcr3(V2P(curproc->pgdir)); // Flush TLB
        return 2; // Success
    }

    return 1; // Unexpected failure
}

// Handle copy-on-write pages
int handle_cow_page(struct proc *curproc, uint *pte, uint physical_addr) {
    char *mem = kalloc();
    if (!mem) {
        cprintf("COW: Allocation failure\n");
        return 1;
    }

    memmove(mem, (char *)P2V(physical_addr), PGSIZE);
    int flags = PTE_FLAGS(*pte) & ~PTE_COW; // Clear COW flag
    flags |= PTE_W;                        // Add write permission
    *pte = V2P(mem) | flags;

    changeRef(physical_addr, 0); // Decrement reference count
    setRef(V2P(mem));            // Increment reference count
    lcr3(V2P(curproc->pgdir));   // Flush TLB

    return 2; // Success
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
case T_PGFLT: {
    uint fault_addr = rcr2(); // Get the faulting address
    struct proc *curproc = myproc();
    uint page_addr = PGROUNDDOWN(fault_addr);
    int result = handle_page_fault(curproc, fault_addr, page_addr);
    
    if (result != 2) {
        cprintf("Segmentation Fault\n");
        curproc->killed = 1;
    }
    break;
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
