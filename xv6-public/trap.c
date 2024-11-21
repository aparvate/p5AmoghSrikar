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

// int cow(uint fault_addr){
//   char *mem;
//   struct proc *p = myproc();
//   int page_addr = PGROUNDDOWN(fault_addr); // Align fault address to page boundary
//   pte_t *pte = walkpgdir(p->pgdir, (void *)page_addr, 0); // Get the PTE
//   if(!pte || !(*pte & PTE_P)) {
//     cprintf("usertrap: invalid access, killing process\n");
//     p->killed = 1;
//   } else if(*pte & PTE_COW){
//     Handle Copy-On-Write
//     uint pa = PTE_ADDR(*pte);
    
//     if(get_ref(pa) > 1){
//       if((mem = kalloc()) == 0){
//         return FAILED;
//       }
//       memmove(mem, (char*)P2V(pa), PGSIZE);
//       *pte = V2P(mem) | PTE_FLAGS(*pte) | PTE_W | PTE_P; // Add PTE_W flag
//       *pte &= ~PTE_COW; // Clear the COW flag
//       dec_ref(pa);
//       set_ref(pa);

//     }else{
//       *pte != PTE_W;
//     }
//     lcr3(V2P(p->pgdir)); // Refresh TLB
//     return SUCCESS;
//   }
//   return FAILED;
// }

// Check if the fault address is part of a mapping
int
lazy_allocate_mapping(uint fault_addr) {
  struct proc *curproc = myproc();

  uint page_addr = PGROUNDDOWN(fault_addr); // Page-aligned address

  // check if reference count is 1, if so, we can write to the page
  //pte_t *pte = walkpgdir(curproc->pgdir, (void *)page_addr, 0);

  // Validate the fault address
  if (IS_VALID_WMAP_ADDR(fault_addr)) {
    //return 0;
  //uint page_addr = PGROUNDDOWN(fault_addr); // Page-aligned address
  

    // Iterate through the mappings to check if the fault address is part of a mapping
    // Only allow the process to access the memory that is part of a mapping
    // Allocate the memory for the mapping if it is not already allocated
    for(int i = 0; i < curproc->wmapinfo.total_mmaps; i++) {
        uint start = curproc->wmapinfo.addr[i]; // Start address of the mapping
        uint end = start + curproc->wmapinfo.length[i]; // End address of the mapping
        if (fault_addr >= start && fault_addr < end) {
            // We will also allocate the memory for the mapping if it is not already allocated right here
            // and then return success, as per lazy allocation
            
            char *mem = kalloc(); // Allocate a page of physical memory
            if (mem == 0) {
                return FAILED;
            }
            memset(mem, 0, PGSIZE); // Zero out the page to prevent information leakage

            // Map the new page with the same permissions as the original page
            if (mappages(curproc->pgdir, (void *)page_addr, PGSIZE, V2P(mem), PTE_U | PTE_W) < 0) {
              cprintf("mappages failed\n");
              kfree(mem);
              curproc->killed = 1;
              return FAILED;
            }

            // Check if the page is file-backed
            if (curproc->wmap_file_info.fd[i] >= 0 && !(curproc->wmap_file_info.flags[i] & MAP_ANONYMOUS)) {
                struct file *f = curproc->ofile[curproc->wmap_file_info.fd[i]];
                // NOTE: We assume that the file is already open, because the file descriptor is valid
                // We also assume the file is of type INODE, as stated in the writeup
                
                if(f){
                  ilock(((struct inode *)f->ip)); // Lock the inode to prevent concurrent writes
                  readi(f->ip, (char*)page_addr, page_addr - start, PGSIZE);
                  iunlock(((struct inode *)f->ip)); // Unlock the inode
                  // Read the page from the file into memory
                  // NOTE: No need to add offset to page_addr - start, as we assume offset is 0
                  // if (readi(((struct inode *)f->ip), mem, page_addr - start, PGSIZE) != PGSIZE) {
                  //     iunlock(((struct inode *)f->ip)); // Unlock the inode
                  //     cprintf("readi failed\n");
                  //     kfree(mem);
                  //     return 1;
                  // }

                }

                

                // NOTE: Recall, we are not responsible for closing the file, because the file descriptor is still open
            }

            // NOTE: Xv6 functions like mappages() already update the PTEs in the page table to set the new physical address
            // along with the permissions, so we do not need to update the PTEs here. Additionally, we need not consider
            // the TLB as the page table entries are already updated.

            // Increment number of pages physically loaded into memory
            curproc->wmapinfo.n_loaded_pages[i]++;

            return SUCCESS; // NOTE: We assume that the mappings are non-overlapping
        }
    }
  }else{
    // Get the POTENTIAL COW FLAGGED page table entry for the fault address for COW handling
    pte_t *pte = walkpgdir(curproc->pgdir, (void *)page_addr, 0);
    uint physical_addr = PTE_ADDR(*pte); // Get the physical address of the page
    if (pte && (*pte & PTE_P) && (*pte & PTE_U)) { // Check if the page table entry is present
      // NOTE: PTE_COW implies PTE_P (refer to guard in cowuvm in vm.c)
      cprintf("This is the page table entry %x", *pte);
      if (!(*pte & PTE_COW) && !(*pte & PTE_W))
      {
        cprintf("does it get in here? \n");
        return FAILED;
      }
      if(*pte & PTE_COW){
        char *mem = kalloc(); // Allocate a page of physical memory
        if (mem == 0) {
          cprintf("Getting in cow: return 0 one\n");
          return FAILED;
        }
        memmove(mem, (char*)P2V(physical_addr), PGSIZE); // Copy the contents of the page to the new page
        int flags = PTE_FLAGS(*pte);
        flags &= ~PTE_COW;
        flags |= PTE_W;
        *pte = V2P(mem) | flags; // Update the PTE to point to the new physical address | TODO: Use mappages() instead?
        dec_ref(physical_addr);
        set_ref(V2P(mem));
      }
      else
      {
        *pte |= PTE_W;
      }
      lcr3(V2P(curproc->pgdir));
      return SUCCESS;


      // if (*pte & PTE_COW) { // Check if the page table entry is present and COW
      //   cprintf("COW page fault\n");

        
      //   // NOTE: kalloc() increments the reference count of the new physical page already
        
        

      //   // Update the page table entry to point to the new physical address
        
      //   lcr3(V2P(curproc->pgdir)); // Refresh the TLB for the new page table entry
      //   dec_ref(physical_addr); // Decrement the reference count of the old physical page, as it is no longer shared

      //   // Free the old physical page if the reference count is 0, as no other process is sharing it
      //   // TODO: This could possibly be handled in dec_ref_count() itself
      //   if (get_ref(physical_addr) == 0) { // If the reference count is 0, free the old page
      //     kfree((char*)P2V(physical_addr));
      //   }
      //   cprintf("is it getting in here? first return cow\n");
      //   return 1; // Return success so that we don't proceed with the default page fault handler (lazy allocation)
      //   // TODO: Double check return
      // } else if (!(*pte & PTE_W)) { // If the page is not COW and not writable (read-only), it is a segmentation fault
      //   // If the page is not COW and not writable, it is a segmentation fault
      //   cprintf("is it getting in here? second lazy allocation return cow\n");
      //   return 1;
      // }
    }

  }
  return FAILED;
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
    // uint fault_addr = rcr2(); 
    // uint addr = PGROUNDDOWN(fault_addr); 
    // struct proc *cproc = myproc();
    // pte_t *pte = walkpgdir(cproc->pgdir, (void*)addr, 0);
    // //uint pfn = get_pfnpa(PTE_ADDR(pte));
    // int ref_count = get_ref(PTE_ADDR(pte));
    // int writeable = PTE_FLAGS(pte) & PTE_W;
    // int was_write = PTE_FLAGS(pte) & PTE_COW;

    // if(writeable){
    //   lazy_allocate_mapping(fault_addr);
    // }else if(was_write != 1){
    //   //cprintf("Segmentation Fault: try to write without permission\n");
    //   cproc->killed = 1;
    //   break;
    // } else if(ref_count == 1){
    //   cprintf("ref count is 1: setting to writable");
    //   *pte |= PTE_W;
    //   *pte &= ~PTE_COW; 
    //   switchkvm();
    // }else if (ref_count > 1) {
    //   // deep copy the page and set it to writeable and flush TLB
    //   char *mem;
    //   uint pa = PTE_ADDR(pte);
    //   int flags = PTE_FLAGS(pte);
    //   if((mem = kalloc()) == 0) {
    //     cprintf("Segmentation Fault: kalloc failed\n");
    //     cproc->killed = 1;
    //     break;
    //   }
    //   memmove(mem, (char*)P2V(pa), PGSIZE);
    //   if(mappages(pte, (void*)addr, PGSIZE, V2P(mem), flags) < 0) {
    //     cprintf("Segmentation Fault: mappages failed\n");
    //     kfree(mem);
    //     cproc->killed = 1;
    //     break;
    //   }
    //   if (*pte & PTE_COW) {
    //     *pte &= ~PTE_COW;
    //     *pte |= PTE_W;
    //     switchkvm();
    //   }

    //   dec_ref(pa);
    // }
    // else {
    //   panic("ref_count <= 0");
    // }

    uint fault_addr = rcr2(); // Get the faulting address

    // cprintf("this is the address %x", fault_addr);
    // if(IS_VALID_WMAP_ADDR(fault_addr)){
    //   if (!lazy_allocate_mapping(fault_addr)) { // lazy allocation
    //     struct proc *curproc = myproc();
    //     cprintf("Segmentation Fault\n");
    //     curproc->killed = 1;
    //     break;
    //   }
    // }else{
    //   if (!cow(fault_addr)) { // lazy allocation
    //     struct proc *curproc = myproc();
    //     cprintf("Segmentation Fault\n");
    //     curproc->killed = 1;
    //     break;
    //   }

    // }

    //uint fault_addr = rcr2(); // Get the faulting address

    if (lazy_allocate_mapping(fault_addr) == -1) { // lazy allocation + copy-on-write
        struct proc *curproc = myproc();
        cprintf("Segmentation Fault\n");
        curproc->killed = 1;
        break;
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
