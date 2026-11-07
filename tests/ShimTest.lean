import VbmSimd.Shims
import VbmSimd.Cursor
import VbmSimd.Find
import VbmSimd.Inset
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
  ins : Nat := 0   -- how many were of the AVX2 membership masks
  app : Nat := 0   -- how many were of the short append

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

/-- The sets the membership masks are tried with: one member (quote, backslash), four distinct (the JSON operators `, : { }`, white space), a repeated slot, the zero byte (the zero that pads past the end must not flag), high bytes. -/
def insetSets : List UInt32 := [0x22222222, 0x5C5C5C5C, 0x7D7B3A2C, 0x5D5B5D5B, 0x0D0A0920, 0x00000000, 0xFF807F00, 0x0D0D0D0A, 0x41424344]

/-- One array, one set, every start: the AVX2 masks against the machine (only on a CPU that has AVX2: the function is the AVX2 body there). -/
def checkInset (st : St) (a : ByteArray) (s : UInt32) (tag : String) : IO St := do
  let mut st := st
  for i in (List.range (a.size + 3)).map (·.toUSize) ++ [0xFFFFFFFF, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF] do
    st ← check st "inset64" (inset64 a i s == insetSpec a i.toNat s) s!"{tag} size {a.size} set {s} i {i}"
    st := { st with ins := st.ins + 1 }
  return st

/-- A byte in none of the insetSets (so a filler cannot flag). -/
def insetFiller (x : UInt64) : UInt8 := let b := (x >>> 24).toUInt8; if insetSets.any (inSet · b) then 0x61 + (b &&& 7) else b

/-- The membership-mask tests (only where the CPU has AVX2, the only place the function is called from): every set; sizes 0 to 140 and the block boundaries; a member planted at each position of a filler array; every byte value
at positions around the lane boundaries (0, 1, 15, 16, 17, 31, 32, 33, 62, 63, 64, 65, size minus one) with starts through the block; every byte a member; random dense arrays. -/
def insetRun (st : St) : IO St := do
  let mut st := st
  unless hasAvx2 () do return st
  let sizes := (List.range 141) ++ [191, 192, 193, 255, 256, 257, 1000]
  for n in sizes do
    for s in insetSets do
      let mut filler := ByteArray.empty
      for _ in [0:n] do
        st := { st with s := next st.s }
        filler := filler.push (insetFiller st.s)
      st ← checkInset st filler s "no member"
      if n ≤ 70 then
        for k in [0:n] do st ← checkInset st (filler.set! k (member s k)) s s!"plant {k}"
      else
        for k in [0, 1, 31, 32, 33, 62, 63, 64, 65, n - 1] do
          if k < n then st ← checkInset st (filler.set! k (member s k)) s s!"plant {k}"
      st ← checkInset st (ByteArray.mk (Array.replicate n s.toUInt8)) s "all members"
      st ← checkInset st (ByteArray.mk (Array.replicate n 0)) s "all zero"
      for _ in [0:3] do
        let mut dense := ByteArray.empty
        for _ in [0:n] do
          st := { st with s := next st.s }
          dense := dense.push (if (st.s >>> 40) % 4 == 0 then member s (st.s >>> 50).toNat else insetFiller st.s)
        st ← checkInset st dense s "dense"
  -- every byte value at the lane and block boundaries, for every set
  for s in insetSets do
    for v in [0:256] do
      for n in [64, 65, 100, 130] do
        for k in [0, 1, 15, 16, 17, 31, 32, 33, 62, 63, 64, 65, n - 1] do
          if k < n then
            let a := (ByteArray.mk (Array.replicate n 0x61)).set! k v.toUInt8
            for i in [0, 1, k - 1, k, 37, 64] do
              st ← check st "inset64 byte value" (inset64 a i.toUSize s == insetSpec a i s) s!"set {s} v {v} n {n} k {k} i {i}"
              st := { st with ins := st.ins + 1 }
  return st

/-- A fresh array of `p` bytes with room for `p + e` (so that the exclusive fast path of `appendBytes` is taken when there is room, and the runtime's when there is none). Not inlined: every call builds a new object. -/
@[noinline] def mkRoom (s : UInt64) (p e : Nat) : ByteArray := Id.run do
  let mut s := s; let mut t := ByteArray.emptyWithCapacity (p + e)
  for _ in [0:p] do s := next s; t := t.push (s >>> 24).toUInt8
  return t

/-- The model of `appendBytes` as plain arrays (`[VS-13]`: `t` followed by `a[i, i + n)`, cut at the end of `a`). -/
def appendModel (t a : ByteArray) (i n : USize) : Array UInt8 := t.data ++ a.data.extract i.toNat (i.toNat + n.toNat)

/-- The short append: the compiled `appendBytes` (the C shim) against the model, on an unshared destination (a fresh array each time) and on a shared one (the original must be untouched), for every combination of a prefix, spare
capacity (none, a little, enough, more than enough), source size, start (through the end and far past it) and length (0 to 20, around 16 and 32, huge). -/
def appendRun (st : St) : IO St := do
  let mut st := st
  let lens : List USize := (List.range 36).map (·.toUSize) ++ [40, 100, 0x7FFFFFFF, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF]
  for asz in [0, 1, 2, 7, 8, 9, 15, 16, 17, 20, 33, 40] do
    let (s', a) := mkArray st.s asz
    st := { st with s := s' }
    let starts : List USize := (List.range (asz + 3)).map (·.toUSize) ++ [0xFFFFFFFF, 0xFFFFFFFFFFFFFFFF]
    for p in [0, 1, 5, 16, 17, 40] do
      for e in [0, 3, 16, 17, 33, 40] do
        for i in starts do
          for n in lens do
            let want := appendModel (mkRoom st.s p e) a i n
            let r := appendBytes (mkRoom st.s p e) a i n
            let rd ← snap r
            st ← check st "appendBytes" (rd == want) s!"asz {asz} prefix {p} room {e} i {i} n {n}"
            -- shared: the destination is still used afterwards
            let t := mkRoom st.s p e
            let t0 ← snap t
            let r2 := appendBytes t a i n
            let r2d ← snap r2
            let t1 ← snap t
            st ← check st "appendBytes shared result" (r2d == want) s!"asz {asz} prefix {p} room {e} i {i} n {n}"
            st ← check st "appendBytes shared original untouched" (t1 == t0) s!"asz {asz} prefix {p} room {e} i {i} n {n}"
            st := { st with app := st.app + 1 }
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
  st ← insetRun st
  st ← appendRun st
  if st.bad == 0 then
    IO.println s!"shim-test: ok ({st.count} comparisons of the C shims against their Lean models; {st.avx} of them the AVX2 search; {st.ins} of them the AVX2 membership masks; {st.app} of them the short append)"
    return 0
  IO.eprintln s!"shim-test: FAILED ({st.bad} of {st.count})"
  return 1

def main : IO UInt32 := run
