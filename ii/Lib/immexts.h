#include <immintrin.h>

int _mm256_put_epi8(__m256i a0) {
  uint8_t v[32];
  _mm256_store_si256((void *) &v , a0);
  return printf("_mm256[%i %i %i %i %i %i %i %i %i %i %i %i %i %i %i %i %i %i %i %i %i %i %i %i %i %i %i %i %i %i %i %i]\n", v[31],v[30],v[29],v[28],v[27],v[26],v[25],v[24],v[23],v[22],v[21],v[20],v[19],v[18],v[17]
  ,v[16],v[15],v[14],v[13],v[12],v[11],v[10],v[9],v[8],v[7],v[6],v[5],v[4],v[3],v[2],v[1],v[0]);
}
