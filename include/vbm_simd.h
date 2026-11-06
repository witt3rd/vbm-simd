/* include/vbm_simd.h: the trusted C of vbm-simd (docs/trust-ledger.md, T10 and T11). Four `static inline` primitives (T10), then the AVX2 byte search and its CPU test (T11), each the C body of an `@[extern]` function of
 * VbmSimd/Shims.lean or VbmSimd/Find.lean whose Lean body is its specification (the model). Include it first in every C file generated from Lean code that calls them
 * (`cc -include include/vbm_simd.h`): Lean then emits only an `extern` prototype after it, which a later declaration of a static function does not conflict with.
 * Every function is total: an access past the end of the array is defined (reads zero, writes nothing there), exactly as the model says; none can touch memory outside the array.
 * Little-endian hosts only (checked below). tests/ShimTest.lean compares each against its model on boundary and random cases. */
#ifndef VBM_SIMD_H
#define VBM_SIMD_H
#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>

#if !defined(__BYTE_ORDER__) || __BYTE_ORDER__ != __ORDER_LITTLE_ENDIAN__
#error "vbm_simd.h: a little-endian host is required"
#endif

/* ld64: the eight bytes at byte offset i as a little-endian u64; bytes at or past the end of `a` read as zero. `a` is borrowed. */
static inline uint64_t vbm_simd_ld64(b_lean_obj_arg a, size_t i) {
  size_t n = lean_sarray_size(a);
  const uint8_t *p = lean_sarray_cptr(a);
  uint64_t w = 0;
  if (i <= n && n - i >= 8) { __builtin_memcpy(&w, p + i, 8); }
  else if (i < n) { for (size_t j = 0; j < n - i; j++) w |= (uint64_t)p[i + j] << (8 * j); }
  return w;
}

/* st64: store w little-endian at byte offset 8*k; bytes past the end are not stored. `out` is consumed: updated in place when exclusive, copied first when shared. */
static inline lean_obj_res vbm_simd_st64(lean_obj_arg out, size_t k, uint64_t w) {
  size_t n = lean_sarray_size(out);
  if (k < n / 8) {
    lean_object *r = lean_sarray_ensure_exclusive(out);
    __builtin_memcpy(lean_sarray_cptr(r) + 8 * k, &w, 8);
    return r;
  }
  if (k < (n + 7) / 8) {
    lean_object *r = lean_sarray_ensure_exclusive(out);
    uint8_t *p = lean_sarray_cptr(r) + 8 * k;
    for (size_t j = 0; j < n - 8 * k; j++) p[j] = (uint8_t)(w >> (8 * j));
    return r;
  }
  return out;
}

/* st32: store w little-endian at byte offset 4*k; bytes past the end are not stored. Ownership as st64. */
static inline lean_obj_res vbm_simd_st32(lean_obj_arg out, size_t k, uint32_t w) {
  size_t n = lean_sarray_size(out);
  if (k < n / 4) {
    lean_object *r = lean_sarray_ensure_exclusive(out);
    __builtin_memcpy(lean_sarray_cptr(r) + 4 * k, &w, 4);
    return r;
  }
  if (k < (n + 3) / 4) {
    lean_object *r = lean_sarray_ensure_exclusive(out);
    uint8_t *p = lean_sarray_cptr(r) + 4 * k;
    for (size_t j = 0; j < n - 4 * k; j++) p[j] = (uint8_t)(w >> (8 * j));
    return r;
  }
  return out;
}

/* ctz: the number of trailing zero bits of x; 64 for x = 0. */
static inline uint64_t vbm_simd_ctz(uint64_t x) { return x ? (uint64_t)__builtin_ctzll(x) : 64; }

/* ---- T11: find the first byte of a set (VS-11): the AVX2 search `vbm_simd_find_avx2` and the CPU test `vbm_simd_has_avx2`. The set `s` is up to four bytes packed in a word (byte k = member k).
 * The result is the index of the first byte of `a` at or after `i` that is a member, `n` (the size) when there is none or `i >= n`: the Lean body `findSpec` is the model. Total: it never reads outside [0, n).
 * Only x86-64 built with clang has the AVX2 body (vector extensions and clang builtins: the Lean toolchain ships no intrinsics header); elsewhere `has_avx2` is 0 and the function is the scalar loop. */
static inline size_t vbm_simd_find_scalar(const uint8_t *p, size_t n, size_t i, uint32_t s) {
  uint8_t b0 = (uint8_t)s, b1 = (uint8_t)(s >> 8), b2 = (uint8_t)(s >> 16), b3 = (uint8_t)(s >> 24);
  for (; i < n; i++) if (p[i] == b0 || p[i] == b1 || p[i] == b2 || p[i] == b3) return i;
  return n;
}
/* The scalar membership mask of the block at `i` (VS-12): the whole function without AVX2, and the short-array case of the AVX2 one. */
static inline uint64_t vbm_simd_inset64_scalar(const uint8_t *p, size_t n, size_t i, uint32_t s) {
  uint8_t b0 = (uint8_t)s, b1 = (uint8_t)(s >> 8), b2 = (uint8_t)(s >> 16), b3 = (uint8_t)(s >> 24);
  uint64_t m = 0;
  if (i >= n) return 0;
  for (size_t j = 0; j < 64 && j < n - i; j++) { uint8_t b = p[i + j]; if (b == b0 || b == b1 || b == b2 || b == b3) m |= (uint64_t)1 << j; }
  return m;
}
#if defined(__x86_64__) && defined(__clang__)
typedef signed char vbm_v32 __attribute__((vector_size(32), aligned(1)));
/* CPUID: AVX2 (leaf 7 ebx bit 5) with the OS saving the vector registers (OSXSAVE and AVX in leaf 1, XCR0 bits 1 and 2). Cached: the answer cannot change while the process runs. */
static inline int vbm_simd_cpu_avx2(void) {
  static int c = -1;
  if (c >= 0) return c;
  unsigned a, b, cx, d; c = 0;
  __asm__ volatile("cpuid" : "=a"(a), "=b"(b), "=c"(cx), "=d"(d) : "0"(0), "2"(0));
  if (a >= 7) {
    __asm__ volatile("cpuid" : "=a"(a), "=b"(b), "=c"(cx), "=d"(d) : "0"(1), "2"(0));
    if ((cx & (1u << 27)) && (cx & (1u << 28))) {
      unsigned lo, hi; __asm__ volatile("xgetbv" : "=a"(lo), "=d"(hi) : "c"(0));
      if ((lo & 6) == 6) { __asm__ volatile("cpuid" : "=a"(a), "=b"(b), "=c"(cx), "=d"(d) : "0"(7), "2"(0)); c = (b >> 5) & 1; }
    }
  }
  return c;
}
/* The 32 bytes at p: bit t of the result is set iff byte t is a member. */
__attribute__((target("avx2"))) static inline uint32_t vbm_simd_members32(const uint8_t *p, uint32_t s) {
  vbm_v32 x, z = {0};
  __builtin_memcpy(&x, p, 32);
  vbm_v32 e = (x == z + (signed char)s) | (x == z + (signed char)(s >> 8)) | (x == z + (signed char)(s >> 16)) | (x == z + (signed char)(s >> 24));
  return (uint32_t)__builtin_ia32_pmovmskb256(e);
}
__attribute__((target("avx2"))) static inline size_t vbm_simd_find_avx2_n(const uint8_t *p, size_t n, size_t i, uint32_t s) {
  if (i >= n) return n;
  while (n - i >= 32) { uint32_t m = vbm_simd_members32(p + i, s); if (m) return i + (size_t)__builtin_ctz(m); i += 32; }
  if (n < 32) return vbm_simd_find_scalar(p, n, i, s);
  /* 0 < n - i < 32: the last 32 bytes of the array (all inside it); the bits of the bytes before i are shifted out */
  uint32_t m = vbm_simd_members32(p + n - 32, s) >> (32 - (n - i));
  return m ? i + (size_t)__builtin_ctz(m) : n;
}
static inline uint8_t vbm_simd_has_avx2(lean_obj_arg u) { (void)u; return (uint8_t)vbm_simd_cpu_avx2(); }
static inline size_t vbm_simd_find_avx2(b_lean_obj_arg a, uint32_t s, size_t i) { return vbm_simd_find_avx2_n(lean_sarray_cptr(a), lean_sarray_size(a), i, s); }
/* ---- T12: membership masks of a block of 64 bytes (VS-12): `vbm_simd_inset64`, the C body of `inset64` (VbmSimd/Inset.lean). Bit p (p < 64) of the result is set iff byte i + p of `a` exists and is a member of the set `s` (up to four
 * bytes packed in a word, as in T11); bits of bytes at or past the end are 0 (so a set that has the byte 0 does not flag the padding), and an `i` at or past the end gives 0. Total: it never reads outside [0, n). The AVX2 body is two
 * 32-byte loads, a compare per member and one movemask each; a block that crosses the end is read as the last 64 bytes of the array (all inside it) with the bits of the bytes before `i` shifted out. */
__attribute__((target("avx2"))) static inline uint64_t vbm_simd_members64(const uint8_t *p, uint32_t s) {
  vbm_v32 x0, x1, z = {0};
  __builtin_memcpy(&x0, p, 32); __builtin_memcpy(&x1, p + 32, 32);
  vbm_v32 c0 = z + (signed char)s, c1 = z + (signed char)(s >> 8), c2 = z + (signed char)(s >> 16), c3 = z + (signed char)(s >> 24);
  vbm_v32 e0 = (x0 == c0) | (x0 == c1) | (x0 == c2) | (x0 == c3);
  vbm_v32 e1 = (x1 == c0) | (x1 == c1) | (x1 == c2) | (x1 == c3);
  return (uint64_t)(uint32_t)__builtin_ia32_pmovmskb256(e0) | ((uint64_t)(uint32_t)__builtin_ia32_pmovmskb256(e1) << 32);
}
__attribute__((target("avx2"))) static inline uint64_t vbm_simd_inset64_avx2_n(const uint8_t *p, size_t n, size_t i, uint32_t s) {
  if (i >= n) return 0;
  size_t r = n - i;
  if (r >= 64) return vbm_simd_members64(p + i, s);
  if (n < 64) return vbm_simd_inset64_scalar(p, n, i, s);
  return vbm_simd_members64(p + n - 64, s) >> (64 - r);
}
static inline uint64_t vbm_simd_inset64(b_lean_obj_arg a, size_t i, uint32_t s) { return vbm_simd_inset64_avx2_n(lean_sarray_cptr(a), lean_sarray_size(a), i, s); }
#else
static inline uint8_t vbm_simd_has_avx2(lean_obj_arg u) { (void)u; return 0; }
static inline size_t vbm_simd_find_avx2(b_lean_obj_arg a, uint32_t s, size_t i) { return vbm_simd_find_scalar(lean_sarray_cptr(a), lean_sarray_size(a), i, s); }
static inline uint64_t vbm_simd_inset64(b_lean_obj_arg a, size_t i, uint32_t s) { return vbm_simd_inset64_scalar(lean_sarray_cptr(a), lean_sarray_size(a), i, s); }
#endif

#endif
