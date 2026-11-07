/* tests/find_guard.c: the byte search of include/vbm_simd.h (trust ledger T11), the membership masks (T12) and the class masks (T14) against a naive loop, on buffers that touch an unmapped page, so that ANY read outside [0, n) is a SIGSEGV and fails
 * the test (an over-read of one byte included: the page before and the page after the buffer are PROT_NONE). Every size 0 to 160, the buffer placed flush against the end of its page and flush
 * against the start of its page (n = 0 puts the pointer on the guard itself), four sets, a member planted at every position and none, every start from 0 to n + 1. The scalar loop is checked
 * on the same cases (it is the whole search on a CPU without AVX2 and the tail of the AVX2 one for short arrays); the AVX2 search only when this CPU has it, the NEON bodies (T15) on aarch64. Built and run by scripts/test-shims.sh. */
#include "vbm_simd.h"
/* The Lean toolchain's compiler ships no libc headers (only its glibc libraries): the five libc functions used are declared here; the values are Linux's, the same on x86-64 and aarch64. On aarch64 the scalar loop and the NEON bodies are checked. */
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

/* bit j of the result: byte i + j exists (below n) and is a member of s */
static uint64_t naive_mask(const uint8_t *p, size_t n, size_t i, uint32_t s) {
  uint64_t m = 0;
  for (size_t j = 0; j < 64 && i + j < n; j++) { uint8_t b = p[i + j]; if (b == (uint8_t)s || b == (uint8_t)(s >> 8) || b == (uint8_t)(s >> 16) || b == (uint8_t)(s >> 24)) m |= (uint64_t)1 << j; }
  return m;
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
  int neon = VBM_SIMD_NEON;   /* the NEON bodies (T15) are compiled on aarch64 with clang: always checked there */
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
#if defined(__aarch64__) && defined(__clang__)
            if (vbm_simd_find_neon_n(p, n, i, s) != want) { bad++; dprintf(2, "find-guard: neon n=%zu i=%zu set=%08x plant=%ld flush=%d\n", n, i, s, plant, flush); }
#endif
            uint64_t wm = naive_mask(p, n, i, s);
            if (vbm_simd_inset64_scalar(p, n, i, s) != wm) { bad++; dprintf(2, "find-guard: inset scalar n=%zu i=%zu set=%08x plant=%ld flush=%d\n", n, i, s, plant, flush); }
#if defined(__x86_64__) && defined(__clang__)
            if (avx && vbm_simd_inset64_avx2_n(p, n, i, s) != wm) { bad++; dprintf(2, "find-guard: inset avx2 n=%zu i=%zu set=%08x plant=%ld flush=%d\n", n, i, s, plant, flush); }
#endif
#if defined(__aarch64__) && defined(__clang__)
            if (vbm_simd_inset64_neon_n(p, n, i, s) != wm) { bad++; dprintf(2, "find-guard: inset neon n=%zu i=%zu set=%08x plant=%ld flush=%d\n", n, i, s, plant, flush); }
#endif
            count++;
          }
        }
      }
  /* The short append (T13). (1) the predicate that decides the fast path, against the plain statement of it in 128-bit arithmetic, on small values and at the edges of size_t; (2) the moves of 0 to 32 bytes on buffers
   * that touch the guard pages (source and destination each flush against the end, or the start, of its page: any byte read or written outside [0, n) is a SIGSEGV) and, in the middle of a page, between sentinels that must
   * not change. */
  {
    const size_t vals[] = {0, 1, 2, 3, 7, 8, 9, 15, 16, 17, 18, 31, 32, 100, (size_t)-3, (size_t)-2, (size_t)-1};
    const size_t nv = sizeof vals / sizeof vals[0];
    for (size_t a = 0; a < nv; a++) for (size_t b = 0; b < nv; b++) for (size_t c = 0; c < nv; c++) for (size_t d = 0; d < nv; d++) for (size_t e = 0; e < nv; e++) {
      size_t ts = vals[a], tc = vals[b], as = vals[c], i = vals[d], n = vals[e];
      int want = n <= 32 && (unsigned __int128)ts <= tc && (unsigned __int128)ts + n <= tc && (unsigned __int128)i <= as && (unsigned __int128)i + n <= as;
      count++;
      if (vbm_simd_append_fits(ts, tc, as, i, n) != want) { bad++; dprintf(2, "find-guard: append fits ts=%zu tc=%zu as=%zu i=%zu n=%zu\n", ts, tc, as, i, n); }
    }
    uint8_t *m2 = mmap(0, 3 * pg, PROT_RW, MAP_PRIVATE_ANON, -1, 0);
    if (m2 == (void *)-1 || mprotect(m2, pg, PROT_NONE) || mprotect(m2 + 2 * pg, pg, PROT_NONE)) { dprintf(2, "find-guard: cannot set up the guard pages\n"); return 2; }
    uint8_t *mid2 = m2 + pg;
    for (int sf = 0; sf < 2; sf++) for (int df = 0; df < 3; df++) for (size_t n = 0; n <= 32; n++) {
      uint8_t *src = sf ? mid + pg - n : mid;                                  /* flush against the end of its page, or its start */
      uint8_t *dst = df == 0 ? mid2 + pg - n : df == 1 ? mid2 : mid2 + 1024;   /* the same; or in the middle of a page, between sentinels */
      for (size_t j = 0; j < n; j++) src[j] = (uint8_t)(0x30 + j * 11);
      if (df == 2) for (long j = -16; j < 64; j++) dst[j] = 0xEE;
      else for (size_t j = 0; j < n; j++) dst[j] = 0xEE;
      vbm_simd_move_short(dst, src, n);
      count++;
      for (size_t j = 0; j < n; j++) if (dst[j] != src[j]) { bad++; dprintf(2, "find-guard: move_short n=%zu byte %zu\n", n, j); break; }
      if (df == 2) {
        for (long j = -16; j < 0; j++) if (dst[j] != 0xEE) { bad++; dprintf(2, "find-guard: move_short wrote before n=%zu at %ld\n", n, j); break; }
        for (long j = (long)n; j < 64; j++) if (dst[j] != 0xEE) { bad++; dprintf(2, "find-guard: move_short wrote past n=%zu at %ld\n", n, j); break; }
      }
    }
  }
  /* The class masks (T14): the scalar words and, for a block wholly inside the array (the case the function dispatches on), the AVX2 words, against a naive loop; the array AND the 32-byte table each flush against the end, and
   * against the start, of their page, so any read outside [0, n) of the array or outside the 32 bytes of the table is a SIGSEGV. */
  {
    uint8_t *m3 = mmap(0, 3 * pg, PROT_RW, MAP_PRIVATE_ANON, -1, 0);
    if (m3 == (void *)-1 || mprotect(m3, pg, PROT_NONE) || mprotect(m3 + 2 * pg, pg, PROT_NONE)) { dprintf(2, "find-guard: cannot set up the guard pages\n"); return 2; }
    uint8_t *mid3 = m3 + pg;
    const uint32_t mss[3] = {0x601C0201, 0xFFFFFFFF, 0x80402010};
    for (int flush = 0; flush < 2; flush++)
      for (size_t n = 0; n <= 200; n++)
        for (int mi = 0; mi < 3; mi++) {
          uint8_t *p = flush ? mid + pg - n : mid;
          uint8_t *t = flush ? mid3 + pg - 32 : mid3;
          for (size_t j = 0; j < 32; j++) t[j] = (uint8_t)(j * 37 + 11 + mi * 5);
          for (size_t j = 0; j < n; j++) p[j] = (uint8_t)(j * 29 + 7 * mi);
          for (size_t i = 0; i <= n + 1; i++) {
            uint64_t want[4], got[4];
            for (int k = 0; k < 4; k++) {
              uint64_t r = 0; uint8_t mk = (uint8_t)(mss[mi] >> (8 * k));
              for (size_t j = 0; j < 64 && i + j < n; j++) { uint8_t v = p[i + j]; if ((uint8_t)(t[v & 15] & t[16 + (v >> 4)] & mk)) r |= (uint64_t)1 << j; }
              want[k] = r;
            }
            vbm_simd_class_words_scalar(p, n, i, t, mss[mi], got);
            for (int k = 0; k < 4; k++) if (got[k] != want[k]) { bad++; dprintf(2, "find-guard: class scalar n=%zu i=%zu mask=%d flush=%d\n", n, i, k, flush); }
#if defined(__x86_64__) && defined(__clang__)
            if (avx && i < n && n - i >= 64) {
              vbm_simd_class_words_avx2(p + i, t, mss[mi], got);
              for (int k = 0; k < 4; k++) if (got[k] != want[k]) { bad++; dprintf(2, "find-guard: class avx2 n=%zu i=%zu mask=%d flush=%d\n", n, i, k, flush); }
            }
#endif
#if defined(__aarch64__) && defined(__clang__)
            if (i < n && n - i >= 64) {
              vbm_simd_class_words_neon(p + i, t, mss[mi], got);
              for (int k = 0; k < 4; k++) if (got[k] != want[k]) { bad++; dprintf(2, "find-guard: class neon n=%zu i=%zu mask=%d flush=%d\n", n, i, k, flush); }
            }
#endif
            count++;
          }
        }
  }
  if (bad) { dprintf(2, "find-guard: FAILED (%zu of %zu)\n", bad, count); return 1; }
  printf("find-guard: ok (%zu cases, avx2 %s, neon %s)\n", count, avx ? "checked" : "not on this cpu", neon ? "checked" : "not on this build");
  return 0;
}
