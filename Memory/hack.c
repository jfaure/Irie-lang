#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/mman.h>

void *memMap(void *hint, size_t size) {
  void *ret = mmap(hint, size , PROT_READ | PROT_WRITE , MAP_PRIVATE | MAP_ANON, -1, 0);
  return ret == MAP_FAILED ? NULL : ret;
}

int pf(char const *x, ...) {
  va_list ap;
  va_start(ap , x);
  int n = printf("\x1b[30m");
  n += vprintf(x , ap);
  n += printf("\x1b[0m");
  return n;
}
#define pf(...)
// 2 ^ 16
#define BUFSIZE 65536
#define PANIC(sz) ({\
  (void)write(2, "Out of Memory\n", 14);\
  exit(1);})

typedef struct Frame* Frame;
// stack of buffers OR tree data (free is linked list of buffers)
struct Frame {
  Frame merge; // if this frame had to grow
  void  *free; // free memory pointer (always <= end)
  void  *end;  // end of this frame

//void  *frags;// for tree data
//int dependents;
};

void *fralloc_isSingle(void *f) { pf("isSingle\n"); return 0; }

// DFTree
void *fralloc_mergeFrames(int n, ...) { pf("fmerge %d\n", n); return NULL; }
void *fralloc_shareFrames(int n, void *f) { pf("fshare %d\n", n); return NULL; }
void *fralloc_freeFrame(void *f) { pf("freeFrame\n"); return f; }
void *fralloc_newFrag(void *f , size_t s) {
  pf("malloc(%ld)\n", s);
  f = malloc(s);
  if (!f) { printf("panic, out of memory"); exit(1); }
  return f;
}
void *fralloc_freeFrag(void *f , void *p, size_t s) { pf("freeFrag\n"); free(p); return f; }

// DFList
void *fralloc_DFList_mergeFrames(int n, ...) { Frame r = malloc(BUFSIZE);
  r->merge = NULL; r->free = r + sizeof(struct Frame); r->end = r + BUFSIZE;
  return r;
}
void *fralloc_push(Frame f , size_t sz) {
  if (f->free + sz < f->end) { void *r = f->free; f->free += sz; return r; }
  PANIC(sz);
}
void *fralloc_pop (Frame f , size_t sz) { f->free -= sz; return f; }

double xd(double x) { return x + 3; }

int test() { return printf("test ok!\n"); }
int putDouble(double x) { return printf("%d\n" , x); }
double times5(double x) { return x * 5; }
void flushStdout() { fflush(stdout); }
