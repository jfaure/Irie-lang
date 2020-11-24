#define LL unsigned long
#define mbinptr DataGroup
#define MALLOC_ALIGNMENT 8

#define fastbin(idx) (g_heap.fast[idx])
// offset 2 for otherwise non-indexable first 2
#define fastbin_index(sz) \
  ((((unsigned int) (sz)) >> (SIZE_SZ == 8 ? 4 : 3)) - 2)
#define MAX_FAST_SIZE  (80 * SIZE_SZ / 4)
#define NFASTBINS (fastbin_index(MAX_FAST_SIZE) + 1)

/*
** bins
*/
#define bin_at(i) (mbinptr) (\
  ((char *) &(g_heap.bins[((i) - 1) * 2]))
// - offsetof (struct DataGroup, free))

#define NBINS             128
#define NSMALLBINS        64
#define SMALLBIN_WIDTH    MALLOC_ALIGNMENT
#define SMALLBIN_CORRECTION (MALLOC_ALIGNMENT > 2 * SIZE_SZ)
#define MIN_LARGE_SIZE    ((NSMALLBINS - SMALLBIN_CORRECTION) * SMALLBIN_WIDTH)
#define in_smallbin_range(sz)  \
  ((LL) (sz) < (LL) MIN_LARGE_SIZE)
#define smallbin_index(sz) \
  ((SMALLBIN_WIDTH == 16 ? (((unsigned) (sz)) >> 4) : (((unsigned) (sz)) >> 3))\
   + SMALLBIN_CORRECTION)
#define BITS64 (SIZE_SZ == 8)
#define largebin_index(sz) (\
   BITS64 && ((((LL) (sz)) >> 6) <= 48) ?  48 + (((LL) (sz)) >> 6)\
 : ((((LL) (sz)) >> 6) <= 38) ?  56 + (((LL) (sz)) >> 6) \
 : ((((LL) (sz)) >> 9) <= 20) ?  91 + (((LL) (sz)) >> 9) \
 : ((((LL) (sz)) >> 12) <= 10) ? 110 +(((LL) (sz)) >> 12)\
 : ((((LL) (sz)) >> 15) <= 4) ? 119 + (((LL) (sz)) >> 15)\
 : ((((LL) (sz)) >> 18) <= 2) ? 124 + (((LL) (sz)) >> 18)\
 : 126)

#define bin_index(sz) ((in_smallbin_range(sz))\
  ? smallbin_index(sz) : largebin_index (sz))

// binmaps (bitvectors)
// Conservatively use 32 bits per map word, even if on 64bit system
#define BINMAPSHIFT      5
#define BITSPERMAP       (1U << BINMAPSHIFT)
#define BINMAPSIZE       (NBINS / BITSPERMAP)
#define idx2block(i)     ((i) >> BINMAPSHIFT)
#define idx2bit(i)       ((1U << ((i) & ((1U << BINMAPSHIFT) - 1))))
#define mark_bin(m, i)   ((m)->binmap[idx2block (i)] |= idx2bit(i))
#define unmark_bin(m, i) ((m)->binmap[idx2block (i)] &= ~(idx2bit(i)))
#define get_binmap(m, i) ((m)->binmap[idx2block (i)] & idx2bit(i))


