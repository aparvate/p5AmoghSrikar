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
  struct proc *curr_p = myproc();

  for(fd = 0; fd < NOFILE; fd++){
    if(curr_p->ofile[fd] == 0){
      curr_p->ofile[fd] = f;
      return fd;
    }
  }
  return -1;
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
  struct proc *curr_p = myproc();

  sz = curr_p->sz;
  if(n > 0){
    if((sz = allocuvm(curr_p->pgdir, sz, sz + n)) == 0)
      return -1;
  } else if(n < 0){
    if((sz = deallocuvm(curr_p->pgdir, sz, sz + n)) == 0)
      return -1;
  }
  curr_p->sz = sz;
  switchuvm(curr_p);
  return 0;
}

// Helper function: copy process state
int
copy_process_state(struct proc *parent, struct proc *child)
{
    if ((child->pgdir = copyuvm(parent->pgdir, parent->sz)) == 0)
        return 0;

    child->sz = parent->sz;
    child->parent = parent;
    *child->tf = *parent->tf;

    copy_file_descriptors(parent, child);
    copy_working_directory(parent, child);
    copy_memory_mappings(parent, child);

    return 1;
}

// Helper function: cleanup on failure
void
cleanup_failed_fork(struct proc *proc)
{
    kfree(proc->kstack);
    proc->kstack = 0;
    proc->state = UNUSED;
}

// Helper function: set up the child's state
void
setup_child_state(struct proc *child)
{
    child->tf->eax = 0; 
}

// Helper function: copy file descriptors
void
copy_file_descriptors(struct proc *parent, struct proc *child)
{
    for (int i = 0; i < NOFILE; i++) {
        if (parent->ofile[i])
            child->ofile[i] = filedup(parent->ofile[i]);
    }
}

// Helper function: copy working directory
void
copy_working_directory(struct proc *parent, struct proc *child)
{
    child->cwd = idup(parent->cwd);
}

// Helper function: copy memory mappings
void
copy_memory_mappings(struct proc *parent, struct proc *child)
{
    child->wmapinfo.total_mmaps = parent->wmapinfo.total_mmaps;

    for (int i = 0; i < parent->wmapinfo.total_mmaps; i++) {
        copy_mapping_info(parent, child, i);
        copy_mapping_pages(parent, child, i);
    }
}

// Helper function: copy mapping info
void
copy_mapping_info(struct proc *parent, struct proc *child, int index)
{
    child->wmapinfo.addr[index] = parent->wmapinfo.addr[index];
    child->wmapinfo.length[index] = parent->wmapinfo.length[index];
    child->wmapinfo.n_loaded_pages[index] = parent->wmapinfo.n_loaded_pages[index];
    child->wmapinfo.flags[index] = parent->wmapinfo.flags[index];

    if (parent->wmapinfo.fd[index] >= 0) {
        struct file *file = parent->ofile[parent->wmapinfo.fd[index]];
        struct file *file_copy = filedup(file);
        child->wmapinfo.fd[index] = fdalloc(file_copy);
    }
}

// Helper function: copy memory-mapped pages
void
copy_mapping_pages(struct proc *parent, struct proc *child, int index)
{
    uint start_addr = parent->wmapinfo.addr[index];
    uint end_addr = start_addr + parent->wmapinfo.length[index];

    for (uint addr = start_addr; addr < end_addr; addr += PGSIZE) {
        uint *pte = walkpgdir(parent->pgdir, (void *)addr, 0);
        if (pte && (*pte & PTE_P)) {
            uint flags = PTE_FLAGS(*pte);
            if (mappages(child->pgdir, (void *)addr, PGSIZE, PTE_ADDR(*pte), flags) < 0) {
                freevm(child->pgdir);
                panic("fork: failed to map pages");
            }
            changeRef(PTE_ADDR(*pte), 1); 
        }
    }
}
// Create a new process copying p as the parent.
// Sets up stack to return as if from system call.
// Caller must set state of returned proc to RUNNABLE.
int
fork(void)
{
    struct proc *curr_p = myproc();
    struct proc *np = allocproc();
    if (!np)
        return -1;

    if (!copy_process_state(curr_p, np)) {
        cleanup_failed_fork(np);
        return -1;
    }

    safestrcpy(np->name, curr_p->name, sizeof(curr_p->name));
    setup_child_state(np);

    acquire(&ptable.lock);
    np->state = RUNNABLE;
    release(&ptable.lock);

    return np->pid;
}

// Exit the current process.  Does not return.
// An exited process remains in the zombie state
// until its parent calls wait() to find out it exited.
void
exit(void)
{
  struct proc *curr_p = myproc();
  struct proc *exit_p;
  int fd;

  if(curr_p == initproc)
    panic("init exiting");

  // Close all open files.
  for(fd = 0; fd < NOFILE; fd++){
    if(curr_p->ofile[fd]){
      fileclose(curr_p->ofile[fd]);
      curr_p->ofile[fd] = 0;
    }
  }

  begin_op();
  iput(curr_p->cwd);
  end_op();
  curr_p->cwd = 0;

  for (uint addr = 0; addr < KERNBASE; addr += PGSIZE) {
      uint8_ts *pte = walkpgdir(curr_p->pgdir, (void *)addr, 0);
        if (pte && (*pte & PTE_P)) {
            uint pa = PTE_ADDR(*pte);
            changeRef(pa, 0);
            *pte = 0;
        }
  }

  acquire(&ptable.lock);

  // Parent might be sleeping in wait().
  wakeup1(curr_p->parent);

  // Pass abandoned children to init.
  struct proc* endAddr = &ptable.proc[NPROC];
  for(exit_p = ptable.proc; exit_p < endAddr; exit_p++){
    if(exit_p->parent == curr_p){
      exit_p->parent = initproc;
      if(exit_p->state == ZOMBIE)
        wakeup1(initproc);
    }
  }
  curr_p->state = ZOMBIE;
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
  struct proc *curr_p = myproc();
  
  acquire(&ptable.lock);
  for(;;){
    // Scan through table looking for exited children.
    havekids = 0;
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->parent != curr_p)
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
    if(!havekids || curr_p->killed){
      release(&ptable.lock);
      return -1;
    }

    // Wait for children to exit.  (See wakeup1 call in proc_exit.)
    sleep(curr_p, &ptable.lock);  //DOC: wait-sleep
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

// wmap system call maps a virtual address to a physical address
uint
wmapHelper(uint start_addr, int size, int map_flags, int file_desc) {
    if (!(map_flags & MAP_FIXED) || !(map_flags & MAP_SHARED)) {
        return FAILED;
    }

    if (size <= 0 || start_addr % PGSIZE != 0) {
        return FAILED;
    }

    if (start_addr < KERNSTART || (start_addr + size) > KERNBASE) {
        return FAILED;
    }

    struct proc *current_process = myproc();
    struct file *file_ptr = NULL;

    if (current_process->wmapinfo.total_mmaps >= MAX_WMMAP_INFO) {
        return FAILED;
    }

    for (int i = 0; i < MAX_WMMAP_INFO; i++) {
        if (current_process->wmapinfo.length[i] != 0) { 
            uint existing_start = current_process->wmapinfo.addr[i];
            uint existing_end = existing_start + current_process->wmapinfo.length[i];
            if (!(start_addr + size <= existing_start || start_addr >= existing_end)) {
                return FAILED; 
            }
        }
    }

    if (!(map_flags & MAP_ANONYMOUS)) {
        if (file_desc < 0 || file_desc >= NOFILE || (file_ptr = current_process->ofile[file_desc]) == NULL) {
            return FAILED;
        }
        filedup(file_ptr);
    }
    int mapping_index = current_process->wmapinfo.total_mmaps;
    current_process->wmapinfo.addr[mapping_index] = start_addr;
    current_process->wmapinfo.length[mapping_index] = size;
    current_process->wmapinfo.n_loaded_pages[mapping_index] = 0; 

    if (map_flags & MAP_ANONYMOUS) {
        current_process->wmapinfo.fd[mapping_index] = -1; 
    } else {
        struct file *duplicated_file = filedup(file_ptr);
        int new_fd = fdalloc(duplicated_file);
        current_process->wmapinfo.fd[mapping_index] = new_fd;
    }

    current_process->wmapinfo.flags[mapping_index] = map_flags;
    current_process->wmapinfo.total_mmaps++;

    return start_addr; 
}

// Helper to write back file-backed mapping
void write_back_mapping(struct proc *curr_p, uint addr, int mapping_index) {
    struct file *file = curr_p->ofile[curr_p->wmapinfo.fd[mapping_index]];
    uint start_addr = addr;
    uint length = curr_p->wmapinfo.length[mapping_index];

    for (uint a = start_addr; a < start_addr + length; a += PGSIZE) {
        begin_op();
        uint *pte = walkpgdir(curr_p->pgdir, (void *)a, 0);
        if (pte && (*pte & PTE_P)) { 
            uint pa = PTE_ADDR(*pte); 
            ilock((struct inode *)file->ip); 
            writei((struct inode *)file->ip, P2V(pa), a - start_addr, PGSIZE);
            iunlock((struct inode *)file->ip);
        }
        end_op();
    }
}

// Helper to unmap pages
void unmap_pages(struct proc *curr_p, uint start_addr, uint length) {
    for (uint a = start_addr; a < start_addr + length; a += PGSIZE) {
        uint *pte = walkpgdir(curr_p->pgdir, (void *)a, 0);
        if (pte && (*pte & PTE_P)) { 
            uint pa = PTE_ADDR(*pte); 
            kfree(P2V(pa));          
            *pte = 0;              
        }
    }
}

// wunmap system call unmaps a virtual address
int
wunmapHelper(uint addr) {
  struct proc *curr_p = myproc();

  for(int i = 0; i <16; i++){
    if ((((addr) % PGSIZE == 0) && ((addr) >= KERNSTART) && ((addr) < KERNBASE))){
      int sharedMap = -1;
      for(uint a = addr; a < (addr + curr_p->wmapinfo.length[i]); a += PGSIZE){
        uint8_ts *pte = walkpgdir(curr_p->pgdir, (void *)a, 0);

        if (pte && (*pte & PTE_P)) {
          uint pa = PTE_ADDR(*pte); 
          changeRef(pa, 0);
          if (getRef(pa) > -1) {
            sharedMap = 1; 
            *pte = 0;
          }
        }
      }
      if (sharedMap == 1) {
        curr_p->wmapinfo.total_mmaps--;
        return 0;
      }
    }
    

  }
  int i;
  for(i = 0; i < curr_p->wmapinfo.total_mmaps; i++) {
      if(curr_p->wmapinfo.addr[i] == addr){
        break;
      }
  }

  if(i == curr_p->wmapinfo.total_mmaps)
    return FAILED;

  if (curr_p->wmapinfo.fd[i] >= 0 && !(curr_p->wmapinfo.flags[i] & MAP_ANONYMOUS)) {
      write_back_mapping(curr_p, addr, i);
  }

  unmap_pages(curr_p, addr, curr_p->wmapinfo.length[i]);

  for (; i < curr_p->wmapinfo.total_mmaps - 1; i++) {
      curr_p->wmapinfo.addr[i] = curr_p->wmapinfo.addr[i + 1];
      curr_p->wmapinfo.length[i] = curr_p->wmapinfo.length[i + 1];
      curr_p->wmapinfo.n_loaded_pages[i] = curr_p->wmapinfo.n_loaded_pages[i + 1];
      curr_p->wmapinfo.fd[i] = curr_p->wmapinfo.fd[i + 1];
      curr_p->wmapinfo.flags[i] = curr_p->wmapinfo.flags[i + 1];
  }

  curr_p->wmapinfo.total_mmaps--;

  return SUCCESS;

}

// va2pa returns the physical address of a virtual address
uint va2paHelper(uint va) {
    struct proc *current_process = myproc(); 
    uint *page_table_entry;
    uint physical_address;

    page_table_entry = walkpgdir(current_process->pgdir, (void *)va, 0);
    if (!page_table_entry || !(*page_table_entry & PTE_P)) {
        return FAILED; 
    }

    uint page_offset = va & 0xFFF; 
    physical_address = PTE_ADDR(*page_table_entry) + page_offset;

    return physical_address;
}


// getwmapinfo system call returns the wmapinfo struct for the current process
int getwmapinfoHelper(struct wmapinfo *user_wmapinfo) {
    struct proc *current_process = myproc(); 

    if (!user_wmapinfo) {
        return FAILED; 
    }
    if (copyout(current_process->pgdir, (uint)user_wmapinfo, (char *)&current_process->wmapinfo, sizeof(struct wmapinfo)) < 0) {
        return FAILED; 
    }
    return SUCCESS; 
}



