/* tests/append_guard.c: the in-place append of include/vbm_simd.h (trust ledger T12) on a hand-built byte array whose spare capacity ends exactly at an unmapped page. Whatever the shim decides, it may write only
 * inside [size, capacity): a store past the capacity is a SIGSEGV and fails the test. The decision itself is checked against the arithmetic of the contract: in place (same object back, bytes behind the old
 * size, size grown) exactly when the array is unshared and n + m <= capacity; otherwise the runtime's append is called (here the runtime is a stand-in that records the call: the real one is the
 * runtime's own and is exercised through Lean by tests/ShimTest.lean) and the array is left untouched. Every n, m and capacity up to 40, unshared and shared. Built and run by scripts/test-shims.sh. */
#include "vbm_simd.h"
extern void *mmap(void *, size_t, int, int, int, long);
extern int mprotect(void *, size_t, int);
extern int printf(const char *, ...);
extern int dprintf(int, const char *, ...);
#define PROT_NONE 0
#define PROT_RW 3
#define MAP_PRIVATE_ANON 0x22

static int calls;
/* the runtime's append, as the shim names it: a stand-in that records that it was asked */
lean_obj_res lean_byte_array_copy_slice(b_lean_obj_arg src, lean_obj_arg so, lean_obj_arg dest, lean_obj_arg dof, lean_obj_arg ln, uint8_t exact) {
  (void)src; (void)so; (void)dof; (void)ln; (void)exact; calls++; return dest;
}

int main(void) {
  size_t pg = 65536;
  uint8_t *m = mmap(0, 3 * pg, PROT_RW, MAP_PRIVATE_ANON, -1, 0);
  if (m == (void *)-1 || mprotect(m, pg, PROT_NONE) || mprotect(m + 2 * pg, pg, PROT_NONE)) { dprintf(2, "append-guard: cannot set up the guard pages\n"); return 2; }
  uint8_t *page = m + pg;
  size_t count = 0, bad = 0;
  for (int shared = 0; shared < 2; shared++)
    for (size_t n = 0; n <= 40; n++)
      for (size_t mm = 0; mm <= 40; mm++)
        for (size_t cap = n; cap <= 40 + 40; cap++) {
          size_t hdr = sizeof(lean_sarray_object);
          lean_sarray_object *a = (lean_sarray_object *)(page + pg - hdr - cap);   /* the data's capacity ends at the page end */
          a->m_header.m_rc = shared ? 2 : 1; a->m_header.m_tag = LeanScalarArray; a->m_header.m_other = 1; a->m_header.m_cs_sz = 0;
          a->m_size = n; a->m_capacity = cap;
          for (size_t i = 0; i < cap; i++) a->m_data[i] = (uint8_t)(0xA0 + i);
          uint8_t bbuf[sizeof(lean_sarray_object) + 64];
          lean_sarray_object *b = (lean_sarray_object *)bbuf;
          b->m_header.m_rc = 1; b->m_header.m_tag = LeanScalarArray; b->m_header.m_other = 1; b->m_header.m_cs_sz = 0; b->m_size = mm; b->m_capacity = mm;
          for (size_t i = 0; i < mm; i++) b->m_data[i] = (uint8_t)(0x30 + i);
          calls = 0;
          lean_object *r = vbm_simd_append((lean_object *)a, (lean_object *)b);
          int inplace = !shared && n + mm <= cap;
          int ok;
          if (inplace) {
            ok = r == (lean_object *)a && calls == 0 && a->m_size == n + mm;
            for (size_t i = 0; ok && i < n; i++) ok = a->m_data[i] == (uint8_t)(0xA0 + i);
            for (size_t i = 0; ok && i < mm; i++) ok = a->m_data[n + i] == (uint8_t)(0x30 + i);
            for (size_t i = n + mm; ok && i < cap; i++) ok = a->m_data[i] == (uint8_t)(0xA0 + i);   /* nothing past the new end was touched */
          } else {
            ok = calls == 1 && r == (lean_object *)a && a->m_size == n && a->m_header.m_rc == (shared ? 2 : 1);
            for (size_t i = 0; ok && i < cap; i++) ok = a->m_data[i] == (uint8_t)(0xA0 + i);
          }
          if (!ok) { bad++; dprintf(2, "append-guard: n=%zu m=%zu cap=%zu shared=%d\n", n, mm, cap, shared); }
          count++;
        }
  if (bad) { dprintf(2, "append-guard: FAILED (%zu of %zu)\n", bad, count); return 1; }
  printf("append-guard: ok (%zu cases)\n", count);
  return 0;
}
