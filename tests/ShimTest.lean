import VbmSimd.Shims
import VbmSimd.Cursor
import VbmSimd.Find
import VbmSimd.Append
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
  avx : Nat := 0   -- how many of the comparisons were of the AVX2 search

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

/-- The sets the search is tried with: LF and CR (a repeated slot), one member, four distinct members including the zero byte and the high bytes, four ASCII delimiters. -/
def findSets : List UInt32 := [0x0D0D0D0A, 0x78787878, 0xFF807F00, 0x5C220A2C]

/-- The CPU test against the kernel's own report (Linux: the `avx2` flag of `/proc/cpuinfo`; where it cannot be read the comparison is skipped). -/
def cpuinfoAvx2 : IO (Option Bool) := do
  try
    let t ← IO.FS.readFile "/proc/cpuinfo"
    let flags := (t.splitOn "\n").filter (·.startsWith "flags")
    if flags.isEmpty then return none
    return some (flags.all fun l => (l.splitOn " ").contains "avx2")
  catch _ => return none

/-- One array, one set, every start: the compiled kernels (AVX2 when the CPU has it, the portable word search, the dispatch) against the machine `findSpec`. -/
def checkFind (st : St) (a : ByteArray) (s : UInt32) (tag : String) : IO St := do
  let mut st := st
  let avx := hasAvx2 ()
  for i in (List.range (a.size + 3)).map (·.toUSize) ++ [0xFFFFFFFF, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF] do
    let spec := findSpec a s i.toNat
    st ← check st "findSwar" (findSwar a s i.toNat == spec) s!"{tag} size {a.size} set {s} i {i}"
    st ← check st "findFirstOf" (findFirstOf a s i.toNat == spec) s!"{tag} size {a.size} set {s} i {i}"
    if avx then
      st ← check st "findAvx2" (findAvx2 a s i == spec.toUSize) s!"{tag} size {a.size} set {s} i {i}"
      st := { st with avx := st.avx + 1 }
  return st

/-- Filler: a byte that is in none of the sets above. -/
def fillerByte (x : UInt64) : UInt8 := let b := (x >>> 24).toUInt8; if findSets.any (inSet · b) then 0x41 + (b &&& 7) else b

def member (s : UInt32) (k : Nat) : UInt8 := match k % 4 with | 0 => s.toUInt8 | 1 => (s >>> 8).toUInt8 | 2 => (s >>> 16).toUInt8 | _ => (s >>> 24).toUInt8

/-- The search tests: the CPU test; for sizes around every step boundary (0 to 70 bytes, 95 to 97, 127 to 129, 255 to 257, 1000) a member planted at every position of a filler array (and none),
a member in every byte, and random arrays dense with members; every start (including past the end and the largest words). -/
def findRun (st : St) : IO St := do
  let mut st := st
  match ← cpuinfoAvx2 with
  | some flag => st ← check st "has_avx2 against cpuinfo" (hasAvx2 () == flag) s!"cpuinfo says {flag}"
  | none => pure ()
  let sizes := (List.range 71) ++ [95, 96, 97, 127, 128, 129, 255, 256, 257, 1000]
  for n in sizes do
    for s in findSets do
      let mut filler := ByteArray.empty
      for _ in [0:n] do
        st := { st with s := next st.s }
        filler := filler.push (fillerByte st.s)
      st ← checkFind st filler s "no member"
      for k in [0:n] do st ← checkFind st (filler.set! k (member s k)) s s!"plant {k}"
      st ← checkFind st (ByteArray.mk (Array.replicate n s.toUInt8)) s "all members"
      for _ in [0:3] do
        let mut dense := ByteArray.empty
        for _ in [0:n] do
          st := { st with s := next st.s }
          dense := dense.push (if (st.s >>> 40) % 16 == 0 then member s (st.s >>> 50).toNat else fillerByte st.s)
        st ← checkFind st dense s "dense"
  return st

/-- A byte array of `n` bytes with room for `spare` more (`emptyWithCapacity` then pushes: unshared, capacity `n + spare`). -/
def withRoom (st : St) (n spare : Nat) : St × ByteArray := Id.run do
  let mut st := st; let mut a := ByteArray.emptyWithCapacity (n + spare)
  for _ in [0:n] do
    st := { st with s := next st.s }
    a := a.push (st.s >>> 24).toUInt8
  return (st, a)

/-- `appendBytes` (the in-place append, `vbm_simd_append`) against its model `a ++ b`, for every pair of sizes 0 to 40, with no spare room (the runtime grows it), exactly enough, one short, plenty; and the
sharing boundary: an array that is still held elsewhere must be copied, never written (the model is a pure function: this is the one thing it cannot say). -/
def appendRun (st : St) : IO St := do
  let mut st := st
  for n in [0:41] do
    for m in [0:41] do
      for spare in [0, m, m + 1, m + 40] do
        let (s1, a) := withRoom st n spare
        let (s2, b) := withRoom s1 m 0
        st := s2
        let a0 ← snap a
        let b0 ← snap b
        let r := appendBytes a b
        let rd ← snap r
        st ← check st "appendBytes" (rd == a0 ++ b0) s!"n {n} m {m} spare {spare}"
      -- shared: the original is read again after the call
      let (s1, a) := withRoom st n m
      let (s2, b) := withRoom s1 m 0
      st := s2
      let a0 ← snap a
      let r := appendBytes a b
      let rd ← snap r
      let a1 ← snap a
      let b0 ← snap b
      st ← check st "appendBytes shared: result" (rd == a0 ++ b0) s!"n {n} m {m}"
      st ← check st "appendBytes shared: original untouched" (a1 == a0) s!"n {n} m {m}"
  return st

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
      -- nextSet at every position (and one past the end): the first set bit of the naive list at or after it, or the end
      let nv := naive b
      let endPos := 64 * VbmSimd.wordCount b
      for j in [0:endPos + 1] do
        let expect := (nv.find? (· ≥ j)).getD endPos
        st ← check st "nextSet" (VbmSimd.nextSet b j == expect) s!"size {n} density {density} j {j}"
  st ← findRun st
  st ← appendRun st
  if st.bad == 0 then
    IO.println s!"shim-test: ok ({st.count} comparisons of the C shims against their Lean models; {st.avx} of them the AVX2 search)"
    return 0
  IO.eprintln s!"shim-test: FAILED ({st.bad} of {st.count})"
  return 1

def main : IO UInt32 := run
