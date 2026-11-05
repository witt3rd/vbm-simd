import VbmSimd.Shims
import VbmSimd.Cursor
/-! # tests/ShimTest.lean: the trusted C shims against their Lean models (Tier 1: `scripts/test-shims.sh`)

Each primitive of `include/vbm_simd.h` (linked in through `lake build shim-test`, which compiles the generated C with `-include include/vbm_simd.h`) is called next to its Lean model on: every array size 0 to 41 with
indices through, at and far past the end (including the largest `USize`), random contents; every single-bit and a few hundred random words; the empty array; a shared array (the shim must copy, never write
the original). A mismatch prints the case and exits 1. The checks cannot be bypassed: they compare the arrays' bytes, not a hash. -/
open VbmSimd

def next (s : UInt64) : UInt64 := let s := s ^^^ (s <<< 13); let s := s ^^^ (s >>> 7); s ^^^ (s <<< 17)

def mkArray (s : UInt64) (n : Nat) : UInt64 × ByteArray := Id.run do
  let mut s := s; let mut a := ByteArray.empty
  for _ in [0:n] do s := next s; a := a.push (s >>> 24).toUInt8
  return (s, a)

structure St where
  s : UInt64
  bad : Nat := 0
  count : Nat := 0

/-- The bytes of `a` now. An IO action, so the compiler can neither merge two snapshots of the same array nor move a snapshot across a store (`a.data` twice would be one value). -/
@[noinline] def snap (a : ByteArray) : BaseIO (Array UInt8) := pure a.data

def check (st : St) (name : String) (ok : Bool) (detail : String) : IO St := do
  if ok then return { st with count := st.count + 1 }
  IO.eprintln s!"shim-test: MISMATCH {name}: {detail}"
  return { st with bad := st.bad + 1, count := st.count + 1 }

/-- All the set positions of `masks` by walking the cursor (the compiled code, with the shims). -/
partial def walk (masks : ByteArray) (w : Nat) (m : UInt64) (acc : Array Nat) : Array Nat :=
  if m == 0 then acc
  else
    let p := VbmSimd.curPos w m
    let (w', m') := VbmSimd.cursorNext masks w m
    walk masks w' m' (acc.push p)

/-- The same by testing every bit position of every byte (the specification, the slow way). -/
def naive (masks : ByteArray) : Array Nat := Id.run do
  let mut r := #[]
  for p in [0:8 * masks.size] do
    if (masks.get! (p / 8) >>> (p % 8).toUInt8) &&& 1 == 1 then r := r.push p
  return r

def run : IO UInt32 := do
  let mut st : St := { s := 0x9E3779B97F4A7C15 }
  let bigs : List USize := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17, 31, 32, 33, 40, 41, 42, 64, 1000, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0x1FFFFFFFFFFFFFFF, 0x2000000000000000, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0xFFFFFFFFFFFFFFF0, 0xFFFFFFFFFFFFFFFF]
  for n in [0:42] do
    let (s', a) := mkArray st.s n
    st := { st with s := s' }
    -- ld64 at every offset (including past the end) and at the huge ones
    for i in (List.range (n + 12)).map (·.toUSize) ++ bigs do
      st ← check st "ld64" (ld64 a i == ld64Model a i.toNat) s!"size {n} i {i}"
    let a0 ← snap a
    for k in (List.range (n / 4 + 6)).map (·.toUSize) ++ bigs do
      st := { st with s := next st.s }
      let w := st.s
      let r := st64 a k w
      let rd ← snap r
      let a1 ← snap a
      st ← check st "st64" (rd == (st64Model (ByteArray.mk a0) k.toNat w).data) s!"size {n} k {k} w {w}"
      st ← check st "st64 original untouched" (a1 == a0) s!"size {n} k {k}"
      let r4 := st32 a k w.toUInt32
      let r4d ← snap r4
      let a2 ← snap a
      st ← check st "st32" (r4d == (st32Model (ByteArray.mk a0) k.toNat w.toUInt32).data) s!"size {n} k {k} w {w.toUInt32}"
      st ← check st "st32 original untouched" (a2 == a0) s!"size {n} k {k}"
  -- the original is not written when shared
  let (s', a) := mkArray st.s 32
  st := { st with s := s' }
  let a0 ← snap a
  let r := st64 a 1 0xFFFFFFFFFFFFFFFF
  let rd ← snap r
  let a1 ← snap a
  let r' := st32 a 2 0xFFFFFFFF
  let rd' ← snap r'
  let a2 ← snap a
  st ← check st "shared array is copied (st64)" (a1 == a0 && rd != a0) "the original changed or the result did not"
  st ← check st "shared array is copied (st32)" (a2 == a0 && rd' != a0) "the original changed or the result did not"
  -- ctz: every single bit, every pair, random words, zero
  st ← check st "ctz 0" (ctz 0 == ctzModel 0 && ctz 0 == 64) "ctz 0"
  for i in [0:64] do
    let x : UInt64 := 1 <<< i.toUInt64
    st ← check st "ctz single bit" (ctz x == ctzModel x && ctz x == i.toUInt64) s!"bit {i}"
    for j in [i:64] do
      let y := x ||| (1 <<< j.toUInt64)
      st ← check st "ctz two bits" (ctz y == ctzModel y) s!"{i} {j}"
  for _ in [0:20000] do
    st := { st with s := next st.s }
    let x := st.s >>> (st.s &&& 63) <<< ((st.s >>> 7) &&& 31)
    st ← check st "ctz random" (ctz x == ctzModel x) s!"{x}"
  -- the cursor (the compiled `cursorStart`/`cursorNext`) against the bit-by-bit enumeration: empty, partial last word, sparse, dense, all-ones, random
  for n in [0:50] do
    for density in [0, 1, 3, 7, 63, 255] do
      let (s', a) := mkArray st.s n
      st := { st with s := s' }
      let mut b := ByteArray.empty
      for i in [0:a.size] do
        st := { st with s := next st.s }
        let byte := if density == 255 then (a.get! i) else if density == 0 then 0 else (a.get! i) &&& (if st.s % (UInt64.ofNat (density + 1)) == 0 then 0xFF else 0)
        b := b.push (if density == 63 then 0xFF else byte)
      let (w0, m0) := VbmSimd.cursorStart b
      st ← check st "cursor" (walk b w0 m0 #[] == naive b) s!"size {n} density {density}"
  if st.bad == 0 then
    IO.println s!"shim-test: ok ({st.count} comparisons of the C shims against their Lean models)"
    return 0
  IO.eprintln s!"shim-test: FAILED ({st.bad} of {st.count})"
  return 1

def main : IO UInt32 := run
