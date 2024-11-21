#include "types.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "x86.h"
#include "proc.h"
#include "spinlock.h"
#include "sleeplock.h"
#include "fs.h"
#include "file.h"

#ifndef NULL
#define NULL ((void *)0)
#endif

struct {
  struct spinlock lock;
  struct proc proc[NPROC];
} ptable;

static struct proc *initproc;

int nextpid = 1;
extern void forkret(void);
extern void trapret(void);

static void wakeup1(void *chan);

static int
fdalloc(struct file *f)
{
  int fd;
  struct proc *curproc = myproc();

  for(fd = 0; fd < NOFILE; fd++){
    if(curproc->ofile[fd] == 0){
      curproc->ofile[fd] = f;
      return fd;
    }
  }
  return -1;
}

// wmap system call maps a virtual address to a physical address
uint
wmap(uint start_addr, int size, int map_flags, int file_desc) {
    // Validate the input flags
    if (!(map_flags & MAP_FIXED) || !(map_flags & MAP_SHARED)) {
        return FAILED;
    }

    // Validate size and address alignment
    if (size <= 0 || start_addr % PGSIZE != 0) {
        return FAILED;
    }

    // Ensure the address is within the valid kernel range
    if (start_addr < KERNSTART || (start_addr + size) > KERNBASE) {
        return FAILED;
    }

    struct proc *current_process = myproc();
    struct file *file_ptr = NULL;

    // Check if the process has reached its mmap limit
    if (current_process->wmapinfo.total_mmaps >= MAX_WMMAP_INFO) {
        return FAILED;
    }

    // Check for overlapping memory mappings
    for (int i = 0; i < MAX_WMMAP_INFO; i++) {
        if (current_process->wmapinfo.length[i] != 0) { // Valid mapping exists
            uint existing_start = current_process->wmapinfo.addr[i];
            uint existing_end = existing_start + current_process->wmapinfo.length[i];
            if (!(start_addr + size <= existing_start || start_addr >= existing_end)) {
                return FAILED; // Overlap detected
            }
        }
    }

    // If not an anonymous mapping, validate and duplicate the file descriptor
    if (!(map_flags & MAP_ANONYMOUS)) {
        if (file_desc < 0 || file_desc >= NOFILE || (file_ptr = current_process->ofile[file_desc]) == NULL) {
            return FAILED;
        }
        filedup(file_ptr); // Increment the file reference count
    }

    // Add the new mapping to the process's wmapinfo structure
    int mapping_index = current_process->wmapinfo.total_mmaps;
    current_process->wmapinfo.addr[mapping_index] = start_addr;
    current_process->wmapinfo.length[mapping_index] = size;
    current_process->wmapinfo.n_loaded_pages[mapping_index] = 0; // Lazy allocation

    // Handle file descriptor and flags for the mapping
    if (map_flags & MAP_ANONYMOUS) {
        current_process->wmapinfo.fd[mapping_index] = -1; // No file backing
    } else {
        struct file *duplicated_file = filedup(file_ptr);
        int new_fd = fdalloc(duplicated_file); // Allocate a new file descriptor
        current_process->wmapinfo.fd[mapping_index] = new_fd;
    }

    current_process->wmapinfo.flags[mapping_index] = map_flags;

    // Increment the total number of mappings
    current_process->wmapinfo.total_mmaps++;

    return start_addr; // Return the starting address of the mapping
}

// wunmap system call unmaps a virtual address
int
wunmap(uint address) {
    struct proc *current_proc = myproc();
    int mapping_index = -1;

    // Validate the address
    if (!((((address) % PGSIZE == 0) && ((address) >= KERNSTART) && ((address) < KERNBASE)))) {
        return FAILED;
    }

    // Locate the mapping to unmap
    for (int i = 0; i < current_proc->wmapinfo.total_mmaps; i++) {
        if (current_proc->wmapinfo.addr[i] == address) {
            mapping_index = i;
            break;
        }
    }

    // Mapping not found
    if (mapping_index == -1) {
        return FAILED;
    }

    // Handle file-backed mappings (MAP_SHARED and not MAP_ANONYMOUS)
    if (current_proc->wmapinfo.fd[mapping_index] >= 0 &&
        !(current_proc->wmapinfo.flags[mapping_index] & MAP_ANONYMOUS)) {
        struct file *file_to_sync = current_proc->ofile[current_proc->wmapinfo.fd[mapping_index]];
        uint map_end = address + current_proc->wmapinfo.length[mapping_index];

        for (uint addr = address; addr < map_end; addr += PGSIZE) {
            uint8_ts *page_table_entry = walkpgdir(current_proc->pgdir, (void *)addr, 0);
            if (page_table_entry && (*page_table_entry & PTE_P)) {
                uint physical_addr = PTE_ADDR(*page_table_entry);
                char *data_to_write = P2V(physical_addr);

                begin_op();
                ilock((struct inode *)file_to_sync->ip);
                writei((struct inode *)file_to_sync->ip, data_to_write, addr - address, PGSIZE);
                iunlock((struct inode *)file_to_sync->ip);
                end_op();
            }
        }
    }

    // Free the memory pages and clear the mapping
    uint map_start = address;
    uint map_end = map_start + current_proc->wmapinfo.length[mapping_index];
    for (uint addr = map_start; addr < map_end; addr += PGSIZE) {
        uint8_ts *page_table_entry = walkpgdir(current_proc->pgdir, (void *)addr, 0);
        if (page_table_entry && (*page_table_entry & PTE_P)) {
            uint physical_addr = PTE_ADDR(*page_table_entry);
            kfree(P2V(physical_addr)); // Free the physical memory
            *page_table_entry = 0;    // Clear the PTE
        }
    }

    // Shift remaining mappings to fill the gap
    for (int i = mapping_index; i < current_proc->wmapinfo.total_mmaps - 1; i++) {
        current_proc->wmapinfo.addr[i] = current_proc->wmapinfo.addr[i + 1];
        current_proc->wmapinfo.length[i] = current_proc->wmapinfo.length[i + 1];
        current_proc->wmapinfo.n_loaded_pages[i] = current_proc->wmapinfo.n_loaded_pages[i + 1];
        current_proc->wmapinfo.fd[i] = current_proc->wmapinfo.fd[i + 1];
        current_proc->wmapinfo.flags[i] = current_proc->wmapinfo.flags[i + 1];
    }

    // Reduce the total mappings count
    current_proc->wmapinfo.total_mmaps--;

    return SUCCESS;
}


// va2pa returns the physical address of a virtual address
uint
va2pa(uint va) {
  uint8_ts *pte;
  uint physical_addr;

  struct proc *curproc = myproc();

  // Get the page table entry for the virtual address
  pte = walkpgdir(curproc->pgdir, (void *)va, 0);
  if(!pte || !(*pte & PTE_P)) {
    return FAILED;
  }

  // Get the physical address from the page table entry
  physical_addr = PTE_ADDR(*pte) + (va & 0xFFF); // TODO: Check alternative version of this calculation
  return physical_addr;
}

// getwmapinfo system call returns the wmapinfo struct for the current process
int
getwmapinfo(struct wmapinfo *wminfo) {
  struct proc *curproc = myproc();

  // Copy the wmapinfo struct to user space
  if(copyout(curproc->pgdir, (uint)wminfo, (char *)&curproc->wmapinfo, sizeof(struct wmapinfo)) < 0)
      return FAILED;

  return SUCCESS;
}

void
pinit(void)
{
  initlock(&ptable.lock, "ptable");
}

// Must be called with interrupts disabled
int
cpuid() {
  return mycpu()-cpus;
}

// Must be called with interrupts disabled to avoid the caller being
// rescheduled between reading lapicid and running through the loop.
struct cpu*
mycpu(void)
{
  int apicid, i;
  
  if(readeflags()&FL_IF)
    panic("mycpu called with interrupts enabled\n");
  
  apicid = lapicid();
  // APIC IDs are not guaranteed to be contiguous. Maybe we should have
  // a reverse map, or reserve a register to store &cpus[i].
  for (i = 0; i < ncpu; ++i) {
    if (cpus[i].apicid == apicid)
      return &cpus[i];
  }
  panic("unknown apicid\n");
}

// Disable interrupts so that we are not rescheduled
// while reading proc from the cpu structure
struct proc*
myproc(void) {
  struct cpu *c;
  struct proc *p;
  pushcli();
  c = mycpu();
  p = c->proc;
  popcli();
  return p;
}

//PAGEBREAK: 32
// Look in the process table for an UNUSED proc.
// If found, change state to EMBRYO and initialize
// state required to run in the kernel.
// Otherwise return 0.
static struct proc*
allocproc(void)
{
  struct proc *p;
  char *sp;

  acquire(&ptable.lock);

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == UNUSED)
      goto found;

  release(&ptable.lock);
  return 0;

found:
  p->state = EMBRYO;
  p->pid = nextpid++;

  release(&ptable.lock);

  // Allocate kernel stack.
  if((p->kstack = kalloc()) == 0){
    p->state = UNUSED;
    return 0;
  }
  sp = p->kstack + KSTACKSIZE;

  // Leave room for trap frame.
  sp -= sizeof *p->tf;
  p->tf = (struct trapframe*)sp;

  // Set up new context to start executing at forkret,
  // which returns to trapret.
  sp -= 4;
  *(uint*)sp = (uint)trapret;

  sp -= sizeof *p->context;
  p->context = (struct context*)sp;
  memset(p->context, 0, sizeof *p->context);
  p->context->eip = (uint)forkret;

  return p;
}

//PAGEBREAK: 32
// Set up first user process.
void
userinit(void)
{
  struct proc *p;
  extern char _binary_initcode_start[], _binary_initcode_size[];

  p = allocproc();
  
  initproc = p;
  if((p->pgdir = setupkvm()) == 0)
    panic("userinit: out of memory?");
  inituvm(p->pgdir, _binary_initcode_start, (int)_binary_initcode_size);
  p->sz = PGSIZE;
  memset(p->tf, 0, sizeof(*p->tf));
  p->tf->cs = (SEG_UCODE << 3) | DPL_USER;
  p->tf->ds = (SEG_UDATA << 3) | DPL_USER;
  p->tf->es = p->tf->ds;
  p->tf->ss = p->tf->ds;
  p->tf->eflags = FL_IF;
  p->tf->esp = PGSIZE;
  p->tf->eip = 0;  // beginning of initcode.S

  safestrcpy(p->name, "initcode", sizeof(p->name));
  p->cwd = namei("/");

  // this assignment to p->state lets other cores
  // run this process. the acquire forces the above
  // writes to be visible, and the lock is also needed
  // because the assignment might not be atomic.
  acquire(&ptable.lock);

  p->state = RUNNABLE;

  release(&ptable.lock);
}

// Grow current process's memory by n bytes.
// Return 0 on success, -1 on failure.
int
growproc(int n)
{
  uint sz;
  struct proc *curproc = myproc();

  sz = curproc->sz;
  if(n > 0){
    if((sz = allocuvm(curproc->pgdir, sz, sz + n)) == 0)
      return -1;
  } else if(n < 0){
    if((sz = deallocuvm(curproc->pgdir, sz, sz + n)) == 0)
      return -1;
  }
  curproc->sz = sz;
  switchuvm(curproc);
  return 0;
}

// Create a new process copying p as the parent.
// Sets up stack to return as if from system call.
// Caller must set state of returned proc to RUNNABLE.
int
fork(void)
{
  int i, pid;
  struct proc *np;
  struct proc *curproc = myproc();

  // Allocate process.
  if((np = allocproc()) == 0){
    return -1;
  }

  // Copy process state from proc.
  if((np->pgdir = copyuvm(curproc->pgdir, curproc->sz)) == 0){
    kfree(np->kstack);
    np->kstack = 0;
    np->state = UNUSED;
    return -1;
  }
  np->sz = curproc->sz;
  np->parent = curproc;
  *np->tf = *curproc->tf;

  // Clear %eax so that fork returns 0 in the child.
  np->tf->eax = 0;

  for(i = 0; i < NOFILE; i++)
    if(curproc->ofile[i])
      np->ofile[i] = filedup(curproc->ofile[i]);
  np->cwd = idup(curproc->cwd);

  // Copy memory mappings from parent to child (mmap regions)
  np->wmapinfo.total_mmaps = curproc->wmapinfo.total_mmaps;
  for (i = 0; i < curproc->wmapinfo.total_mmaps; i++) {
    // Copy memory mapping information
    np->wmapinfo.addr[i] = curproc->wmapinfo.addr[i];
    np->wmapinfo.length[i] = curproc->wmapinfo.length[i];
    np->wmapinfo.n_loaded_pages[i] = curproc->wmapinfo.n_loaded_pages[i];

    // Copy file info for file-backed mappings.
    np->wmapinfo.fd[i] = curproc->wmapinfo.fd[i];
    np->wmapinfo.flags[i] = curproc->wmapinfo.flags[i];
    if (curproc->wmapinfo.fd[i] >= 0) {
      struct file *f = curproc->ofile[curproc->wmapinfo.fd[i]];
      struct file *copy = filedup(f);
      int newFd = fdalloc(copy);
      np->wmapinfo.fd[i] = newFd;
    }
    // Map the same virtual -> physical mappings for the child process.
    for (uint addr = curproc->wmapinfo.addr[i]; addr < curproc->wmapinfo.addr[i] + curproc->wmapinfo.length[i]; addr += PGSIZE) {
      uint8_ts *pte = walkpgdir(curproc->pgdir, (void *)addr, 0);
      uint flags = PTE_FLAGS(*pte);
      if (pte && (*pte & PTE_P)) { // Check if page is present.
        // Map the page in the child’s page table
        if (mappages(np->pgdir, (void *)addr, PGSIZE, PTE_ADDR(*pte), flags) < 0) {
          freevm(pte);
          return -1;
        }
        // Increment reference count for the shared page.
        inc_ref(PTE_ADDR(*pte));
      }
      
    }
  }

  safestrcpy(np->name, curproc->name, sizeof(curproc->name));

  pid = np->pid;

  acquire(&ptable.lock);

  np->state = RUNNABLE;

  release(&ptable.lock);


  return pid;
}

// Exit the current process.  Does not return.
// An exited process remains in the zombie state
// until its parent calls wait() to find out it exited.
void
exit(void)
{
  struct proc *curproc = myproc();
  struct proc *p;
  int fd;

  if(curproc == initproc)
    panic("init exiting");

  // Close all open files.
  for(fd = 0; fd < NOFILE; fd++){
    if(curproc->ofile[fd]){
      fileclose(curproc->ofile[fd]);
      curproc->ofile[fd] = 0;
    }
  }

  begin_op();
  iput(curproc->cwd);
  end_op();
  curproc->cwd = 0;

  // Decrement reference counts and free physical pages if necessary.
  for (uint addr = 0; addr < KERNBASE; addr += PGSIZE) {
      uint8_ts *pte = walkpgdir(curproc->pgdir, (void *)addr, 0);
        if (pte && (*pte & PTE_P)) {
            uint pa = PTE_ADDR(*pte);
            dec_ref(pa);
            // if(get_ref(pa) == 0){
            //   kfree((char*) pa);
            //   *pte = 0;
            // }
            *pte = 0;
        }
  }

  acquire(&ptable.lock);

  // Parent might be sleeping in wait().
  wakeup1(curproc->parent);

  // Pass abandoned children to init.
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->parent == curproc){
      p->parent = initproc;
      if(p->state == ZOMBIE)
        wakeup1(initproc);
    }
  }

  // Jump into the scheduler, never to return.
  curproc->state = ZOMBIE;
  sched();
  panic("zombie exit");
}

// Wait for a child process to exit and return its pid.
// Return -1 if this process has no children.
int
wait(void)
{
  struct proc *p;
  int havekids, pid;
  struct proc *curproc = myproc();
  
  acquire(&ptable.lock);
  for(;;){
    // Scan through table looking for exited children.
    havekids = 0;
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->parent != curproc)
        continue;
      havekids = 1;
      if(p->state == ZOMBIE){
        // Found one.
        pid = p->pid;
        kfree(p->kstack);
        p->kstack = 0;
        freevm(p->pgdir);
        p->pid = 0;
        p->parent = 0;
        p->name[0] = 0;
        p->killed = 0;
        p->state = UNUSED;
        release(&ptable.lock);
        return pid;
      }
    }

    // No point waiting if we don't have any children.
    if(!havekids || curproc->killed){
      release(&ptable.lock);
      return -1;
    }

    // Wait for children to exit.  (See wakeup1 call in proc_exit.)
    sleep(curproc, &ptable.lock);  //DOC: wait-sleep
  }
}

//PAGEBREAK: 42
// Per-CPU process scheduler.
// Each CPU calls scheduler() after setting itself up.
// Scheduler never returns.  It loops, doing:
//  - choose a process to run
//  - swtch to start running that process
//  - eventually that process transfers control
//      via swtch back to the scheduler.
void
scheduler(void)
{
  struct proc *p;
  struct cpu *c = mycpu();
  c->proc = 0;
  
  for(;;){
    // Enable interrupts on this processor.
    sti();

    // Loop over process table looking for process to run.
    acquire(&ptable.lock);
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->state != RUNNABLE)
        continue;

      // Switch to chosen process.  It is the process's job
      // to release ptable.lock and then reacquire it
      // before jumping back to us.
      c->proc = p;
      switchuvm(p);
      p->state = RUNNING;

      swtch(&(c->scheduler), p->context);
      switchkvm();

      // Process is done running for now.
      // It should have changed its p->state before coming back.
      c->proc = 0;
    }
    release(&ptable.lock);

  }
}

// Enter scheduler.  Must hold only ptable.lock
// and have changed proc->state. Saves and restores
// intena because intena is a property of this
// kernel thread, not this CPU. It should
// be proc->intena and proc->ncli, but that would
// break in the few places where a lock is held but
// there's no process.
void
sched(void)
{
  int intena;
  struct proc *p = myproc();

  if(!holding(&ptable.lock))
    panic("sched ptable.lock");
  if(mycpu()->ncli != 1)
    panic("sched locks");
  if(p->state == RUNNING)
    panic("sched running");
  if(readeflags()&FL_IF)
    panic("sched interruptible");
  intena = mycpu()->intena;
  swtch(&p->context, mycpu()->scheduler);
  mycpu()->intena = intena;
}

// Give up the CPU for one scheduling round.
void
yield(void)
{
  acquire(&ptable.lock);  //DOC: yieldlock
  myproc()->state = RUNNABLE;
  sched();
  release(&ptable.lock);
}

// A fork child's very first scheduling by scheduler()
// will swtch here.  "Return" to user space.
void
forkret(void)
{
  static int first = 1;
  // Still holding ptable.lock from scheduler.
  release(&ptable.lock);

  if (first) {
    // Some initialization functions must be run in the context
    // of a regular process (e.g., they call sleep), and thus cannot
    // be run from main().
    first = 0;
    iinit(ROOTDEV);
    initlog(ROOTDEV);
  }

  // Return to "caller", actually trapret (see allocproc).
}

// Atomically release lock and sleep on chan.
// Reacquires lock when awakened.
void
sleep(void *chan, struct spinlock *lk)
{
  struct proc *p = myproc();
  
  if(p == 0)
    panic("sleep");

  if(lk == 0)
    panic("sleep without lk");

  // Must acquire ptable.lock in order to
  // change p->state and then call sched.
  // Once we hold ptable.lock, we can be
  // guaranteed that we won't miss any wakeup
  // (wakeup runs with ptable.lock locked),
  // so it's okay to release lk.
  if(lk != &ptable.lock){  //DOC: sleeplock0
    acquire(&ptable.lock);  //DOC: sleeplock1
    release(lk);
  }
  // Go to sleep.
  p->chan = chan;
  p->state = SLEEPING;

  sched();

  // Tidy up.
  p->chan = 0;

  // Reacquire original lock.
  if(lk != &ptable.lock){  //DOC: sleeplock2
    release(&ptable.lock);
    acquire(lk);
  }
}

//PAGEBREAK!
// Wake up all processes sleeping on chan.
// The ptable lock must be held.
static void
wakeup1(void *chan)
{
  struct proc *p;

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == SLEEPING && p->chan == chan)
      p->state = RUNNABLE;
}

// Wake up all processes sleeping on chan.
void
wakeup(void *chan)
{
  acquire(&ptable.lock);
  wakeup1(chan);
  release(&ptable.lock);
}

// Kill the process with the given pid.
// Process won't exit until it returns
// to user space (see trap in trap.c).
int
kill(int pid)
{
  struct proc *p;

  acquire(&ptable.lock);
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->pid == pid){
      p->killed = 1;
      // Wake process from sleep if necessary.
      if(p->state == SLEEPING)
        p->state = RUNNABLE;
      release(&ptable.lock);
      return 0;
    }
  }
  release(&ptable.lock);
  return -1;
}

//PAGEBREAK: 36
// Print a process listing to console.  For debugging.
// Runs when user types ^P on console.
// No lock to avoid wedging a stuck machine further.
void
procdump(void)
{
  static char *states[] = {
  [UNUSED]    "unused",
  [EMBRYO]    "embryo",
  [SLEEPING]  "sleep ",
  [RUNNABLE]  "runble",
  [RUNNING]   "run   ",
  [ZOMBIE]    "zombie"
  };
  int i;
  struct proc *p;
  char *state;
  uint pc[10];

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->state == UNUSED)
      continue;
    if(p->state >= 0 && p->state < NELEM(states) && states[p->state])
      state = states[p->state];
    else
      state = "???";
    cprintf("%d %s %s", p->pid, state, p->name);
    if(p->state == SLEEPING){
      getcallerpcs((uint*)p->context->ebp+2, pc);
      for(i=0; i<10 && pc[i] != 0; i++)
        cprintf(" %p", pc[i]);
    }
    cprintf("\n");
  }
}



