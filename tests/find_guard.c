/* tests/find_guard.c: the byte search of include/vbm_simd.h (trust ledger T11) against a naive loop, on buffers that touch an unmapped page, so that ANY read outside [0, n) is a SIGSEGV and fails
 * the test (an over-read of one byte included: the page before and the page after the buffer are PROT_NONE). Every size 0 to 160, the buffer placed flush against the end of its page and flush
 * against the start of its page (n = 0 puts the pointer on the guard itself), four sets, a member planted at every position and none, every start from 0 to n + 1. The scalar loop is checked
 * on the same cases (it is the whole search on a CPU without AVX2 and the tail of the AVX2 one for short arrays); the AVX2 search only when this CPU has it. Built and run by scripts/test-shims.sh. */
#include "vbm_simd.h"
/* The Lean toolchain's compiler ships no libc headers (only its glibc libraries): the five libc functions used are declared here; the values are Linux's, the same on x86-64 and aarch64. On aarch64 there is no AVX2 body: only the scalar loop is checked. */
extern void *mmap(void *, size_t, int, int, int, long);
extern int mprotect(void *, size_t, int);
extern int printf(const char *, ...);
extern int dprintf(int, const char *, ...);
#define PROT_NONE 0
#define PROT_RW 3
#define MAP_PRIVATE_ANON 0x22

static size_t naive(const uint8_t *p, size_t n, size_t i, uint32_t s) {
  for (; i < n; i++) { uint8_t b = p[i]; if (b == (uint8_t)s || b == (uint8_t)(s >> 8) || b == (uint8_t)(s >> 16) || b == (uint8_t)(s >> 24)) return i; }
  return n;
}

int main(void) {
  size_t pg = 65536;   /* a multiple of every page size in use */
  uint8_t *m = mmap(0, 3 * pg, PROT_RW, MAP_PRIVATE_ANON, -1, 0);
  if (m == (void *)-1 || mprotect(m, pg, PROT_NONE) || mprotect(m + 2 * pg, pg, PROT_NONE)) { dprintf(2, "find-guard: cannot set up the guard pages\n"); return 2; }
  uint8_t *mid = m + pg;
  const uint32_t sets[4] = {0x0D0D0D0A, 0x78787878, 0xFF807F00, 0x5C220A2C};
#if defined(__x86_64__) && defined(__clang__)
  int avx = vbm_simd_cpu_avx2();
#else
  int avx = 0;
#endif
  size_t count = 0, bad = 0;
  for (int flush = 0; flush < 2; flush++)
    for (size_t n = 0; n <= 160; n++)
      for (int si = 0; si < 4; si++) {
        uint32_t s = sets[si];
        uint8_t *p = flush ? mid + pg - n : mid;
        for (long plant = -1; plant < (long)n; plant++) {
          for (size_t j = 0; j < n; j++) p[j] = (uint8_t)(0x41 + (j * 7) % 13);   /* filler: ASCII letters, in no set */
          if (plant >= 0) p[plant] = (uint8_t)(s >> (8 * (plant % 4)));
          for (size_t i = 0; i <= n + 1; i++) {
            size_t want = naive(p, n, i, s);
            if (vbm_simd_find_scalar(p, n, i, s) != want) { bad++; dprintf(2, "find-guard: scalar n=%zu i=%zu set=%08x plant=%ld flush=%d\n", n, i, s, plant, flush); }
#if defined(__x86_64__) && defined(__clang__)
            if (avx && vbm_simd_find_avx2_n(p, n, i, s) != want) { bad++; dprintf(2, "find-guard: avx2 n=%zu i=%zu set=%08x plant=%ld flush=%d\n", n, i, s, plant, flush); }
#endif
            count++;
          }
        }
      }
  if (bad) { dprintf(2, "find-guard: FAILED (%zu of %zu)\n", bad, count); return 1; }
  printf("find-guard: ok (%zu cases, avx2 %s)\n", count, avx ? "checked" : "not on this cpu");
  return 0;
}
