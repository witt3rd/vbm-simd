import VbmSimd.Shims
/-! # `VbmSimd.Cursor`: walking the set bits of a mask array, in order, without materialising an index

A scanner turns a text into a mask array (one 64-bit word per 64 bytes, a set bit for each interesting position); its consumer wants the positions of the set bits, one at a time, in order. A cursor is a word index `w` and
`m`, the bits of word `w` not yet consumed: the next position is `64 * w + ctz m`, consuming it is `m &&& (m - 1)`, and when `m` is empty the cursor moves on to the next non-empty word. No allocation, no index array.
Carry `w` and `m` as two loop arguments (not as a pair that is returned from a non-inlined function) to keep them unboxed.
Proved against the list of set positions (`[VS-7]`, `VbmSimdProofs.Cursor`): the positions the cursor yields, in order, are exactly the set bits of the words. -/
namespace VbmSimd

/-- `x` with its lowest set bit cleared (`blsr` on x86-64). -/
@[inline] def clearLowest (x : UInt64) : UInt64 := x &&& (x - 1)

/-- The number of 64-bit words in a mask array (a partial last word counts; bytes past the end read as zero). -/
@[inline] def wordCount (masks : ByteArray) : Nat := (masks.size + 7) / 8

/-- Word `w` of the mask array (little-endian; zero past the end), by one load. -/
@[inline] def wordAt (masks : ByteArray) (w : Nat) : UInt64 := ld64 masks (8 * w).toUSize

/-- Normalise a cursor: while `m` is empty and there is a later word, move to it (`f` is fuel; `n` the word count). The result has `m ≠ 0`, or no later word. -/
def seek (masks : ByteArray) (n : Nat) : Nat → Nat → UInt64 → Nat × UInt64
  | 0, w, m => (w, m)
  | f + 1, w, m => if m == 0 && w + 1 < n then seek masks n f (w + 1) (wordAt masks (w + 1)) else (w, m)

/-- The position (in bits) the cursor `(w, m)` stands at: valid when `m ≠ 0`. -/
@[inline] def curPos (w : Nat) (m : UInt64) : Nat := 64 * w + (ctz m).toNat

/-- The cursor at the start of the mask array. -/
@[inline] def cursorStart (masks : ByteArray) : Nat × UInt64 := seek masks (wordCount masks) (wordCount masks) 0 (wordAt masks 0)

/-- The cursor after consuming the position `curPos w m` (`m ≠ 0`). -/
@[inline] def cursorNext (masks : ByteArray) (w : Nat) (m : UInt64) : Nat × UInt64 :=
  seek masks (wordCount masks) (wordCount masks) w (clearLowest m)

end VbmSimd
