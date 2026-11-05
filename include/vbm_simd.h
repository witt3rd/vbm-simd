/* include/vbm_simd.h: the trusted C of vbm-simd (docs/trust-ledger.md, T10). Four `static inline` primitives, each the C body of an `@[extern]` function of
 * VbmSimd/Shims.lean whose Lean body is its specification (the model). Include it first in every C file generated from Lean code that calls them
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

#endif
