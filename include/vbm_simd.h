/* include/vbm_simd.h: the trusted C of vbm-simd (docs/trust-ledger.md, T10, T11, T12 and T13). Four `static inline` primitives (T10), then the AVX2 byte search and its CPU test (T11), each the C body of an `@[extern]` function of
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

/* ---- T13: append a short run of bytes (VS-13): `vbm_simd_append`, the C body of `appendBytes` (VbmSimd/Append.lean). The model is the runtime's `copySlice` at the end of the destination: the result is the same value either way.
 * The fast path needs: n <= 32, the run inside `a` (i + n <= its size), room in `t` (size + n <= its capacity) and `t` unshared; it moves the n bytes with two loads and two stores that overlap (reading only a[i, i + n),
 * writing only t[size, size + n)) and sets the new size. Anything else is the runtime's lean_byte_array_copy_slice, which cuts a run at the end of `a`, grows `t` and copies it when it is shared.
 * The call is not inlined (`noinline`): in a consumer's parse loop, which uses it at several sites, the inlined body measured slower than a call (code size and register pressure of the loop). */
static inline int vbm_simd_append_fits(size_t ts, size_t tc, size_t as, size_t i, size_t n) {
  return n <= 32 && ts <= tc && n <= tc - ts && i <= as && n <= as - i;
}
static inline void vbm_simd_move_short(uint8_t *d, const uint8_t *s, size_t n) {   /* n <= 32: reads s[0, n), writes d[0, n) */
  if (n >= 16) {
    uint64_t x0, x1, y0, y1;
    __builtin_memcpy(&x0, s, 8); __builtin_memcpy(&x1, s + 8, 8); __builtin_memcpy(&y0, s + n - 16, 8); __builtin_memcpy(&y1, s + n - 8, 8);
    __builtin_memcpy(d, &x0, 8); __builtin_memcpy(d + 8, &x1, 8); __builtin_memcpy(d + n - 16, &y0, 8); __builtin_memcpy(d + n - 8, &y1, 8);
  }
  else if (n >= 8) { uint64_t x, y; __builtin_memcpy(&x, s, 8); __builtin_memcpy(&y, s + n - 8, 8); __builtin_memcpy(d, &x, 8); __builtin_memcpy(d + n - 8, &y, 8); }
  else if (n >= 4) { uint32_t x, y; __builtin_memcpy(&x, s, 4); __builtin_memcpy(&y, s + n - 4, 4); __builtin_memcpy(d, &x, 4); __builtin_memcpy(d + n - 4, &y, 4); }
  else if (n >= 2) { uint16_t x, y; __builtin_memcpy(&x, s, 2); __builtin_memcpy(&y, s + n - 2, 2); __builtin_memcpy(d, &x, 2); __builtin_memcpy(d + n - 2, &y, 2); }
  else if (n == 1) d[0] = s[0];
}
extern lean_obj_res lean_byte_array_copy_slice(b_lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg, uint8_t);   /* the runtime's (lean.h does not declare it; the generated C does, with the same type) */
/* The general case, in a function of its own: the three conversions of a size to a Lean number (a call each when the value is past the boxed range) need callee-saved registers, which the fast path then no longer pays for in a prologue. */
static __attribute__((noinline)) lean_obj_res vbm_simd_append_slow(lean_obj_arg t, b_lean_obj_arg a, size_t i, size_t n) {
  return lean_byte_array_copy_slice(a, lean_usize_to_nat(i), t, lean_usize_to_nat(lean_sarray_size(t)), lean_usize_to_nat(n), 0);
}
static inline __attribute__((noinline)) lean_obj_res vbm_simd_append(lean_obj_arg t, b_lean_obj_arg a, size_t i, size_t n) {
  size_t ts = lean_sarray_size(t);
  if (__builtin_expect(vbm_simd_append_fits(ts, lean_sarray_capacity(t), lean_sarray_size(a), i, n) && lean_is_exclusive(t), 1)) {
    vbm_simd_move_short(lean_sarray_cptr(t) + ts, lean_sarray_cptr(a) + i, n);
    lean_sarray_set_size(t, ts + n);
    return t;
  }
  return vbm_simd_append_slow(t, a, i, n);
}

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
/* ---- T14: the class masks of a block of 64 bytes (VS-14): `vbm_simd_classify64`, the C body of `classify64` (VbmSimd/Classify.lean). A byte v has the class bits t[v & 15] & t[16 + (v >> 4)] (`t`: 32 bytes of nibble tables; the
 * model reads zero past the end of the Lean array, so a shorter one is zero-padded here); mask r (byte r of `ms`) has bit j set iff byte i + j exists (below n) and its class bits meet that mask byte. The four masks are stored as
 * the words 0 to 3 of `out` (in place when unshared, copied first when shared), a word only where all its eight bytes lie inside `out`. Total: it never reads outside [0, n) of `a` nor outside the 32 bytes of the table, and
 * never writes outside `out`. The AVX2 body (clang, x86-64) is two 32-byte loads, two byte shuffles and a compare per mask and half; a block that does not lie wholly inside the array, and every other build, is the scalar loop. */
static inline uint64_t vbm_simd_class_scalar(const uint8_t *p, size_t n, size_t i, const uint8_t *t, uint8_t m) {
  uint64_t r = 0;
  if (i >= n) return 0;
  for (size_t j = 0; j < 64 && j < n - i; j++) { uint8_t v = p[i + j]; if ((uint8_t)(t[v & 15] & t[16 + (v >> 4)] & m)) r |= (uint64_t)1 << j; }
  return r;
}
static __attribute__((noinline)) void vbm_simd_class_words_scalar(const uint8_t *p, size_t n, size_t i, const uint8_t *t, uint32_t ms, uint64_t w[4]) {
  for (int k = 0; k < 4; k++) w[k] = vbm_simd_class_scalar(p, n, i, t, (uint8_t)(ms >> (8 * k)));
}
/* The four words stored at the start of `out`, each only where it lies wholly inside (the slow path: an `out` of less than 32 bytes). */
static __attribute__((noinline)) lean_obj_res vbm_simd_put4_slow(lean_obj_arg out, const uint64_t w[4]) {
  size_t n = lean_sarray_size(out);
  if (n < 8) return out;
  lean_object *r = lean_sarray_ensure_exclusive(out);
  uint8_t *q = lean_sarray_cptr(r);
  for (size_t k = 0; k < 4 && 8 * k + 8 <= n; k++) __builtin_memcpy(q + 8 * k, &w[k], 8);
  return r;
}
static inline lean_obj_res vbm_simd_put4(lean_obj_arg out, uint64_t w0, uint64_t w1, uint64_t w2, uint64_t w3) {
  if (lean_sarray_size(out) >= 32) {
    lean_object *r = lean_sarray_ensure_exclusive(out);
    uint8_t *q = lean_sarray_cptr(r);
    __builtin_memcpy(q, &w0, 8); __builtin_memcpy(q + 8, &w1, 8); __builtin_memcpy(q + 16, &w2, 8); __builtin_memcpy(q + 24, &w3, 8);
    return r;
  }
  const uint64_t w[4] = {w0, w1, w2, w3};
  return vbm_simd_put4_slow(out, w);
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
/* T14: the AVX2 body. `p` has 64 readable bytes. The tables are broadcast to both 128-bit lanes (the byte shuffle works within a lane); the low nibbles are `x & 15`, the high nibbles `(x >> 4) & 15` (a 16-bit shift: the bits that
 * cross from the neighbour byte are cleared by the mask), each used as the shuffle index, and the class bits are the and of the two lookups. A mask is `(class & m) != 0` per byte, by a compare with zero and a movemask, inverted. */
typedef signed char vbm_v16 __attribute__((vector_size(16), aligned(1)));
typedef unsigned short vbm_w16 __attribute__((vector_size(32), aligned(1)));
__attribute__((target("avx2"))) static inline void vbm_simd_class_words_avx2(const uint8_t *p, const uint8_t *t, uint32_t ms, uint64_t w[4]) {
  vbm_v16 l16, h16;
  __builtin_memcpy(&l16, t, 16); __builtin_memcpy(&h16, t + 16, 16);
  vbm_v32 lo = __builtin_shufflevector(l16, l16, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15);
  vbm_v32 hi = __builtin_shufflevector(h16, h16, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15);
  vbm_v32 z = {0}, nib = z + 15;
  vbm_v32 m0 = z + (signed char)ms, m1 = z + (signed char)(ms >> 8), m2 = z + (signed char)(ms >> 16), m3 = z + (signed char)(ms >> 24);
  uint64_t r0 = 0, r1 = 0, r2 = 0, r3 = 0;
  for (int h = 0; h < 2; h++) {
    vbm_v32 x, xh;
    __builtin_memcpy(&x, p + 32 * h, 32);
    xh = (vbm_v32)((vbm_w16)x >> 4);
    vbm_v32 c = (vbm_v32)__builtin_ia32_pshufb256(lo, x & nib) & (vbm_v32)__builtin_ia32_pshufb256(hi, xh & nib);
    uint32_t e0 = (uint32_t)__builtin_ia32_pmovmskb256((c & m0) == z), e1 = (uint32_t)__builtin_ia32_pmovmskb256((c & m1) == z);
    uint32_t e2 = (uint32_t)__builtin_ia32_pmovmskb256((c & m2) == z), e3 = (uint32_t)__builtin_ia32_pmovmskb256((c & m3) == z);
    r0 |= (uint64_t)(uint32_t)~e0 << (32 * h); r1 |= (uint64_t)(uint32_t)~e1 << (32 * h); r2 |= (uint64_t)(uint32_t)~e2 << (32 * h); r3 |= (uint64_t)(uint32_t)~e3 << (32 * h);
  }
  w[0] = r0; w[1] = r1; w[2] = r2; w[3] = r3;
}
__attribute__((target("avx2"))) static __attribute__((noinline)) lean_obj_res vbm_simd_classify64_avx2_n(const uint8_t *p, size_t n, size_t i, const uint8_t *t, uint32_t ms, lean_obj_arg out) {
  uint64_t w[4];
  if (i < n && n - i >= 64) vbm_simd_class_words_avx2(p + i, t, ms, w); else vbm_simd_class_words_scalar(p, n, i, t, ms, w);
  return vbm_simd_put4(out, w[0], w[1], w[2], w[3]);
}
static inline lean_obj_res vbm_simd_classify64(b_lean_obj_arg a, size_t i, b_lean_obj_arg tb, uint32_t ms, lean_obj_arg out) {
  uint8_t pad[32] = {0};
  const uint8_t *t = lean_sarray_cptr(tb);
  size_t ts = lean_sarray_size(tb);
  if (ts < 32) { for (size_t j = 0; j < ts; j++) pad[j] = t[j]; t = pad; }
  return vbm_simd_classify64_avx2_n(lean_sarray_cptr(a), lean_sarray_size(a), i, t, ms, out);
}
#else
static inline uint8_t vbm_simd_has_avx2(lean_obj_arg u) { (void)u; return 0; }
static inline size_t vbm_simd_find_avx2(b_lean_obj_arg a, uint32_t s, size_t i) { return vbm_simd_find_scalar(lean_sarray_cptr(a), lean_sarray_size(a), i, s); }
static inline uint64_t vbm_simd_inset64(b_lean_obj_arg a, size_t i, uint32_t s) { return vbm_simd_inset64_scalar(lean_sarray_cptr(a), lean_sarray_size(a), i, s); }
static inline lean_obj_res vbm_simd_classify64(b_lean_obj_arg a, size_t i, b_lean_obj_arg tb, uint32_t ms, lean_obj_arg out) {
  uint8_t pad[32] = {0};
  const uint8_t *t = lean_sarray_cptr(tb);
  size_t ts = lean_sarray_size(tb);
  if (ts < 32) { for (size_t j = 0; j < ts; j++) pad[j] = t[j]; t = pad; }
  uint64_t w[4];
  vbm_simd_class_words_scalar(lean_sarray_cptr(a), lean_sarray_size(a), i, t, ms, w);
  return vbm_simd_put4(out, w[0], w[1], w[2], w[3]);
}
#endif

#endif
