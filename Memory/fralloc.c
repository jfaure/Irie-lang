/*
** Nimzo Allocator
** designed to exploit it's understanding
** of nimzo allocation patterns
**
** New: Arg always have frame
** Frame == DG means it is fixed size (never shared or reffed)
*/

#include <unistd.h>
#include <stdlib.h>
#include <sys/mman.h>
#include "bins.h"
// TODO add windows compatible mmap weak symbol
// TODO size classes

typedef int SizeT;
typedef int BitMap;
#define CHUNK void*
#define FRAG  void*
#define false 0
#define true 1
#define bool char
typedef struct Heap* Heap;
typedef struct MMap* MMap;
typedef struct DataGroup* DataGroup;
typedef struct FreeDataGroup* FreeDataGroup;
typedef struct Frame* Frame;
typedef struct Frag* Frag;

void *memMap(void *hint, size_t size) {
  void *ret = mmap(hint, size , PROT_READ | PROT_WRITE , MAP_PRIVATE | MAP_ANON, -1, 0);
  return (ret == MAP_FAILED ? NULL : ret)
}
//if (munmap(addr, size) == -1) return;

/*
** Heap
*/
#define ALIGN_MASK (2*SIZE_SZ - 1)
// minsize SIZE_SZ + ALIGN_MASK
#define request2size(req)\
  (((req) + SIZE_SZ + ALIGN_MASK) & ~ALIGN_MASK)
#define SIZE_SZ (sizeof(size_t))


struct Heap {
  // we hint the kernel to give contiguous mmaps
  void *mmapEnd; // end of last mapping

  DataGroup large;
  FreeDataGroup fast[NFASTBINS];
  FreeDataGroup bins[NBINS * 2 - 2];
  unsigned int binmap[BINMAPSIZE];

  void (*panic)(size_t);
} g_heap;

#define PANIC(sz) ({ if (g_heap.panic)\
  { g_heap.panic(sz); } else {\
  (void)write(2, "Out of Memory\n", 14);\
  exit(1);}})

/*
** DataGroup
*/
struct DataGroup {
//size_t prevSize; set if (not PREV_IN_USE)
  size_t sz;  // usually ARENA_SZ

  // iff (! FIXED_SIZE)
  DataGroup merge;
  Frame frames;
};

struct FreeDataGroup {
  size_t sz;
  DataGroup next;
  DataGroup prev; // only set in largebins
};

#define PREV_IN_USE(sz) ((1U << 1))
#define FIXEDSIZE(sz)   ((1U << 2))
#define MMAPPED(sz)     ((1U << 3))
#define PREVSIZE(d)     (( (size_t*) d)[-1])
#define NEXTDG(d)       ((char*)d + d->size)
#define DG_MINSIZE\
  request2size(sizeof(struct DataGroup))
#define MEM2DG(m) ((DataGroup) (m - SIZE_SZ))
#define DG2MEM(m) (m + SIZE_SZ)

/*
** Frame
*/
struct Frame { // Fixed size frame ?! (Frame == DG) perhaps
  Frame merge;
  Frag  frags;

  // size classes ?
  int dependents;
  struct {
    size_t sz; Frame reffed[];
  } refs;
};
#define Frame2mem(f) (&f->sz)
#define Frag2mem(f) (f + sizeof(struct Frag))
#define ARENA_SZ 0xffff
#define ALIGN_ARENA(ptr) (ptr & (!ARENA_SZ))

/*
** Frag
*/
// ? size classes
struct Frag {
  size_t sz;
  Frag le;
  Frag eq;
};

#define dgFromMem(mem, sz) mem
#define dgNew(sz) _dgNew(request2size(sz))
#define dgSingleton(sz) DG2MEM(dgNew)

static inline void
dgTrim(DataGroup d, size_t size) {
  if (d->sz - size > DG_MINSIZE) {
    DataGroup split = (DataGroup) (d + size);
//  g_heap.large = d->next;
//  g_heap.large->prev = d->prev;
  }
}

DataGroup
_dgNew(size_t sz) { // sz already normalized
  FreeDataGroup bin;
  DataGroup d;

  // 1. Fastbins
  if (sz <= MAX_FAST_SIZE
    && (bin = &fastbin(fastbin_index(sz)))
    || in_smallbin_range(sz)
    && (bin = &bin_at(smallbin_index(sz)))
    ) {
    d = (DataGroup) *bin;
    *bin = bin->next;
    return d;
  }

  // 2. LargeBins
  if (NULL) {
    return dgTrim(d, sz);
  }

  // 4. sysmalloc ; try to map contiguous space
  d = memMap(g_heap.mmapEnd, ARENA_SZ);
  if (!d)
    PANIC(sz);
  g_heap.mmapEnd += sz;
  d->next = NULL;
  return d;
}

void
sdgTrim(DataGroup d, size_t trimSz) {
  if (trimSz < MALLOC_ALIGNMENT)
    return;
}

void
dgTrim(DataGroup d) {
  if (d->frames) {
    size_t trimSz = 0;
    return dgTrim(MEM2DG(d) , trimSz);
  }
}

void
dgFree(DataGroup d) {
  size_t s = d->sz;
  while (!PREV_IN_USE(d)) { // coalesce
    d -= PREVSIZE(d);
    d->size = s;
  }
//d->next = g_heap->large;
//g_heap->large = d;
}

/*
** Frames
*/
Frame[]
newFrames(DataGroup d, int n, size_t *sizes) {
  // multithreaded case (worse for fragmentation)
}

Frame
newFrame(DataGroup d, size_t minsize) {
  Frame ret = d->free;
  if (ret) {
    d->free = ret->free;
    return ret;
  }
  return (newFrame(newDataGroup() , minsize));
}

Frame
merge(DataGroup d, int argCount, Frame args[],
     size_t size, bool flat) {
// make retframe out of the to-be reffed argframes
// retFrames are a spaghetti of reffed arg frames
// ? retframes usually outlive argframes ?
  size += argCount * sizeof(Frame)
        + sizeof(struct Frame);
  Frame r = newFrame(d, size);
  r->dependents = 0;
  r->merge = NULL;
//r->next  = ;
  r->refCount = argCount;
  while (--argCount > 0)
    r->reffed[argCount] = args[argCount];
  return r;
}

void
trimFrame(DataGroup d, Frame f1, Frame f2) {
// f2 no longer expects to grow
// try to merge into f1
//if (f2 == f1->frags + f1->frags->sz) {
//f1->frags->sz +=
//  f2->frags->sz + (sizeof(struct Frame));
//return f1;
//}
// add to freeFrame list TODO
}

void
growFrame(DataGroup d, Frame f) {
// for flat data: attempt mmap right after Frame
}

void
delFrame(DataGroup d, Frame f) {
// dec refcounts; maybe return Frames to datagroup
  if (--f->dependents > 0)
    return;
  // also del reffed
//Frame t=f;
//while (t->reffed != f) {
//  if (delFrame(d, t->reffed)) //unlink dependent
//    t->reffed = t->reffed->reffed;
//    t=t->reffed;
//  }
}

/*
** Frags
*/
CHUNK
newFrag(int sz, DataGroup d, Frame f) {
  // try the frame's frags, else the datagroup
  // TODO rbtree
  int residue;
  Frag ret , p = f->frags;
  if (p && sz > p->sz) {
    while (p->le && sz > p->le->sz)
      p = p->le;
    ret = p->le;
    p->le = p->le->le;
    residue = ret->sz - sz;
    if (residue > sizeof(struct Frag))
      delFrag((Frag) (ret + sz) , residue);
    else
      f->next = NULL;
    return ret;
    }
  // fallback to datagroup
  return newFrag(sz, d, newFrame(d , 0));
}

// eg. unlinking elements from tree structures
// if frontend wants to reuse these, call delFrag
void
delFrag(Frame f, void *newFrag, int sz) {
  // note frag sizes are usually very limited
  Frag p = f->frags , new = (Frag) newFrag;
  new->sz = sz;
  if (!p) {
    new->le = new->eq = NULL;
    f->frags = new;
    return;
  }
  while (p->le && sz >= p->le->sz)
    p = p->le;
  if (sz == p->sz) {
    new->eq = p->eq; // no need to set le
    p->eq = new;
    }
  else {
    new->eq = NULL;
    new->le = p->le;
    p->le = new;
  }
}

int main()
{
  DataGroup d[10];
  Frame f[10];

  d[0] = dgNew(5);
  d[1] = dgNew(1000);
  dgFree(d[0]);
  dgTrim(d[1] , 5);
  dgFree(d[0]);
}
