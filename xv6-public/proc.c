#include "types.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "x86.h"
#include "proc.h"
#include "spinlock.h"
#include "wmap.h"
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

int
wmapHelper(uint addr, int length, int flags, int fd) {
  if (!(flags & MAP_FIXED) || !(flags & MAP_SHARED)) {
    return FAILED;
  }
  if (length <= 0) {
    return FAILED;
  }
  if (addr % PGSIZE != 0) {
    return FAILED;
  }
  if (addr < KERNSTART || addr + length > KERNBASE) {
    return FAILED;
  }

  struct proc* curr_p = myproc();
  struct file *file;

  // Handle anonymous mapping case
  if (flags & MAP_ANONYMOUS) {
    file = NULL;
  } else {
    if (fd < 0 || fd >= NOFILE || (file = curr_p->ofile[fd]) == NULL) {
      return FAILED;
    }
  }

  // Check if region is already allocated or available
  for (uint a = addr; a < addr + length; a += PGSIZE) {
    pte_t *pte = walkpgdir(curr_p->pgdir, (char *)a, 0);
    if (pte && (*pte & PTE_P)) {
      return FAILED;
    }
  }

  struct map_wmap *map = NULL;

  // Find the first empty slot in the mappings array
  for (int i = 0; i < 16; i++) {
    if (curr_p->maps[i].length == 0) {
      map = &curr_p->maps[i];
      break;
    }
  }

  if (map == NULL) {
    return FAILED;
  }

  // Dynamically calculate the next available address if not MAP_FIXED
  if (!(flags & MAP_FIXED)) {
    addr = KERNSTART;
    for (int i = 0; i < 16; i++) {
      struct map_wmap *existing = &curr_p->maps[i];
      if (existing->length > 0) {
        uint end = existing->addr + existing->length;
        if (addr < end) {
          addr = end; // Move addr past the end of this mapping
        }
      }
    }
    if (addr + length > KERNBASE) {
      return FAILED; // Out of address space
    }
  }

  // Fill in the mapping details
  map->addr = addr;
  map->length = length;
  map->flags = flags;
  map->file = file;
  map->fd = fd;

  // Mark the pages for lazy allocation
  for (uint a = addr; a < addr + length; a += PGSIZE) {
    pte_t *pte = walkpgdir(curr_p->pgdir, (char *)a, 1);
    *pte = 0; // Mark the page as not present
  }

  return addr;
}



int wunmapHelper(uint addr) {
  struct proc *curr_p = myproc();
  struct map_wmap *map = NULL;

  // Validate address alignment
  if (addr % PGSIZE != 0) {
    return FAILED;
  }

  // Find the mapping corresponding to the given address
  for (int i = 0; i < 16; i++) {
    if (curr_p->maps[i].addr == addr) {
      map = &curr_p->maps[i];
      break;
    }
  }

  // If no matching mapping is found, return failure
  if (map == NULL) {
    return FAILED;
  }

  // Handle file-backed mappings with MAP_SHARED
  if (map->file && (map->flags & MAP_SHARED)) {
    uint offset = 0;
    for (uint a = map->addr; a < map->addr + map->length; a += PGSIZE, offset += PGSIZE) {
      pte_t *pte = walkpgdir(curr_p->pgdir, (char *)a, 0);
      if (pte && (*pte & PTE_P)) {
        char *data = (char *)P2V(PTE_ADDR(*pte));
        begin_op();
        ilock(map->file->ip);
        writei(map->file->ip, data, offset, PGSIZE);
        iunlock(map->file->ip);
        end_op();
      }
    }
  }

  // Free allocated pages
  for (uint a = map->addr; a < map->addr + map->length; a += PGSIZE) {
    pte_t *pte = walkpgdir(curr_p->pgdir, (char *)a, 0);
    if (pte && (*pte & PTE_P)) {
      uint pa = PTE_ADDR(*pte);
      kfree(P2V(pa)); // Free the physical memory
      *pte = 0;       // Clear the PTE
    }
  }

  // Clear the mapping metadata
  map->addr = 0;
  map->length = 0;
  map->flags = 0;
  map->file = NULL;
  map->fd = -1;

  // Flush the TLB to ensure no stale entries
  lcr3(V2P(curr_p->pgdir));

  return SUCCESS; // Success
}


int va2paHelper(uint va){
    struct proc *curproc = myproc(); // Get the current process
    pde_t *pgdir = curproc->pgdir;  // Get the page directory of the process

    // Translate the virtual address to the corresponding physical address
    pte_t *pte = walkpgdir(pgdir, (const void *)va, 0);

    // If the PTE doesn't exist or the page isn't present, return -1
    if (!pte || !(*pte & PTE_P)) {
        return -1;
    }

    // Extract the physical page address from the PTE
    uint pa = PTE_ADDR(*pte);

    // Add the offset within the page
    uint offset = va & 0xFFF; // Lower 12 bits of the virtual address

    return pa | offset; // Combine the physical page address with the offset
}

int getwmapinfoHelper(struct wmapinfo *wminfo) {
    struct proc *curproc = myproc(); // Get the current process
    if (!curproc) {
        return FAILED; // No valid process context
    }

    if (!wminfo) {
        return FAILED; // Invalid pointer to wmapinfo struct
    }

    int mmap_count = 0; // Counter for total memory mappings

    // Initialize the wmapinfo structure
    wminfo->total_mmaps = 0;
    for (int i = 0; i < MAX_WMMAP_INFO; i++) {
        wminfo->addr[i] = 0;
        wminfo->length[i] = 0;
        wminfo->n_loaded_pages[i] = 0;
    }

    // Iterate over all memory mappings in the current process
    for (int i = 0; i < 16; i++) {
        struct map_wmap *map = &curproc->maps[i];

        // Skip unused or invalid mappings
        if (map->addr == 0 || map->length <= 0) {
            continue;
        }

        // Check if we've exceeded MAX_WMMAP_INFO
        if (mmap_count >= MAX_WMMAP_INFO) {
            return FAILED; // Too many memory mappings
        }

        // Populate address and length in the wmapinfo struct
        wminfo->addr[mmap_count] = map->addr;
        wminfo->length[mmap_count] = map->length;

        // Calculate the number of loaded pages for this mapping
        int loaded_pages = 0;
        for (uint a = map->addr; a < map->addr + map->length; a += PGSIZE) {
            pte_t *pte = walkpgdir(curproc->pgdir, (char *)a, 0);

            if (pte && (*pte & PTE_P)) {
                loaded_pages++;
            } else if (pte && !(*pte & PTE_P)) {
                // Optional: Handle cases where pages are allocated but not present
                continue;
            }
        }
        wminfo->n_loaded_pages[mmap_count] = loaded_pages;

        mmap_count++;
    }

    // Update the total_mmaps field
    wminfo->total_mmaps = mmap_count;

    return SUCCESS; // Successfully populated the wmapinfo struct
}


