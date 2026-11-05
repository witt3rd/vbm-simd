/-! # `VbmSimd.Spec`: the specifications, as one-bit-at-a-time machines

A word-parallel kernel is *correct* when it computes, for all 64 bit positions at once, what a tiny sequential machine computes one position at a time. The machines are
the definition of correct; they are small enough to read. Each carries a spec-clause tag `[VS-n]` (listed in `docs/SPEC.md`; the theorems that discharge a clause quote the tag,
and Tier 1 checks that the two lists agree).

Bit `i` of a word is bit `i` counting from the least significant bit; a block of 64 bytes is read little-endian, so byte `k` of the block is bits `8k .. 8k+7`. -/
namespace VbmSimd

/-- Bit `i` of `x` (`false` past the top). -/
@[inline] def bit (x : UInt64) (i : Nat) : Bool := x.toBitVec.getLsbD i

/-- `[VS-1]` the prefix-xor machine: the state after bit `i` is the xor of bits `0 .. i` of `x`. -/
def scanXor (x : UInt64) : Nat → Bool
  | 0 => bit x 0
  | i + 1 => scanXor x i ^^ bit x (i + 1)

/-- `[VS-2]` the escape machine: `escSpec b pb i` is true iff byte `i` of the block is *escaped*, i.e. the byte before it is a backslash (bit of `b`) that is not itself escaped.
`pb` says that byte 0 is escaped by the last byte of the previous block (the carry). The state after the last byte (`escSpec b pb 64`) is the carry into the next block. -/
def escSpec (b : UInt64) (pb : Bool) : Nat → Bool
  | 0 => pb
  | i + 1 => bit b i && !escSpec b pb i

/-- A carry as a word: `1` when set, `0` otherwise (the form the kernels take and give). -/
@[inline] def carryWord (c : Bool) : UInt64 := if c then 1 else 0

/-- Byte `k` of a word (bits `8k .. 8k+7`), as a bit vector. -/
def byte (w : UInt64) (k : Nat) : BitVec 8 := w.toBitVec.extractLsb' (8 * k) 8

/-- `[VS-3]` the lane-equality predicate: byte `k` of `w` equals byte `k` of `c`. With `c` a byte repeated in every lane this is "byte `k` of `w` is that byte". -/
def laneEq (c w : UInt64) (k : Nat) : Bool := decide (byte w k = byte c k)

/-- `[VS-4]` the flag of lane `k` of a mask that carries one flag per byte lane, in the top bit of the lane (bit `8k + 7`). -/
def laneFlag (m : UInt64) (k : Nat) : Bool := bit m (8 * k + 7)

/-- The positions `i`, in increasing order, of the set bits of `m`, searched from `i` for `f` more bits (the machine behind `[VS-7]`). -/
def posFrom (m : UInt64) : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, i => if bit m i then i :: posFrom m f (i + 1) else posFrom m f (i + 1)

/-- The positions of the set bits of `m`, increasing. -/
def bitsOf (m : UInt64) : List Nat := posFrom m 64 0

/-- All set positions (counted in bits from the start of the mask array) of the words `w .. n - 1` of the mask words `ws`, increasing. -/
def streamFrom (ws : Nat → UInt64) (n : Nat) (w : Nat) : List Nat :=
  if w < n then (bitsOf (ws w)).map (64 * w + ·) ++ streamFrom ws n (w + 1) else []
termination_by n - w

/-- `[VS-7]` the stream a bit cursor stands for: the set bits of `m` (the not yet consumed part of word `w`), then every set bit of the later words. -/
def curStream (ws : Nat → UInt64) (n : Nat) (w : Nat) (m : UInt64) : List Nat :=
  (bitsOf m).map (64 * w + ·) ++ streamFrom ws n (w + 1)

/-- A set of at most four bytes, packed in a word: byte `k` of `s` (bits `8k .. 8k+7`) is member `k`; repeat a byte to fill a slot that is not needed. -/
def inSet (s : UInt32) (b : UInt8) : Bool := b == s.toUInt8 || b == (s >>> 8).toUInt8 || b == (s >>> 16).toUInt8 || b == (s >>> 24).toUInt8

/-- `[VS-11]` the find machine: the index of the first byte of `a` at or after `i` that is in the set `s`; `a.size` when there is none (and when `i` is not below the end). One byte per step. -/
def findSpec (a : ByteArray) (s : UInt32) (i : Nat) : Nat :=
  if h : i < a.size then (if inSet s a[i] then i else findSpec a s (i + 1)) else a.size
termination_by a.size - i

/-- `[VS-12]` the append machine: the bytes of `a`, then the bytes of `b`. -/
def appendSpec (a b : ByteArray) : List UInt8 := a.data.toList ++ b.data.toList

end VbmSimd
