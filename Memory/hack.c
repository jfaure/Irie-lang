#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>

int pf(char const *x, ...) {
  va_list ap;
  va_start(ap , x);
  int n = printf("\x1b[30m");
  n += vprintf(x , ap);
  n += printf("\x1b[0m");
  return n;
}
#define pf

void *fralloc_mergeFrames(int n, ...) { pf("fmerge %d\n", n); return NULL; }
void *fralloc_shareFrames(int n, void *f) { pf("fshare %d\n", n); return NULL; }
void *fralloc_freeFrame(void *f) { pf("freeFrame\n"); return f; }
void *fralloc_isSingle(void *f) { pf("isSingle\n"); return 0; }
void *fralloc_newFrag(void *f , size_t s) {
  pf("malloc(%ld)\n", s);
  f = malloc(s);
  if (!f) { printf("panic, out of memory"); exit(1); }
  return f;
}
void *fralloc_freeFrag(void *f , void *p, size_t s) { pf("freeFrag\n"); free(p); return f; }
