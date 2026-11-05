import VbmSimd.Spec
/-! # `VbmSimd.Escape`: which bytes of a block are escaped by a backslash (the add-with-carry trick)

A backslash escapes the byte after it unless it is itself escaped, so a run of `k` backslashes escapes the byte after the run iff `k` is odd. Finding the odd runs of a 64-bit mask is a
carry chain: add the run starts (of one parity) to the backslash mask and the carry ripples to the end of the run. Two additions, one per parity of the start position, give
the ends of the odd runs; the carry out of the top bit is the escape state handed to the next block. Proved against the machine `escSpec` (`[VS-2]`): `VbmSimdProofs.Escape`. -/
namespace VbmSimd

/-- The mask of the even bit positions (0, 2, 4, ...). -/
@[inline] def evenBits : UInt64 := 0x5555555555555555
/-- The mask of the odd bit positions (1, 3, 5, ...). -/
@[inline] def oddBits : UInt64 := 0xAAAAAAAAAAAAAAAA

/-- The escaped positions of the block, for the bytes that are not themselves backslashes (`escaped_spec`): bit `i` is `escSpec b pb i`. `b` is the backslash mask,
`prev` the carry in (`carryWord pb`). At a position that holds a backslash the bit is unspecified (the consumer, `quote and not escaped`, never asks). -/
@[inline] def escaped (b prev : UInt64) : UInt64 :=
  let bs := b &&& ~~~prev
  let starts := bs &&& ~~~(bs <<< 1)
  let endsEv := (bs + (starts &&& evenBits)) &&& ~~~bs
  let endsOd := (bs + (starts &&& oddBits)) &&& ~~~bs
  (endsEv &&& oddBits) ||| (endsOd &&& evenBits) ||| prev

/-- The carry out of the block (`escOut_spec`): `1` when an odd run of backslashes reaches the last byte, so the first byte of the next block is escaped. -/
@[inline] def escOut (b prev : UInt64) : UInt64 :=
  let bs := b &&& ~~~prev
  let starts := bs &&& ~~~(bs <<< 1)
  if bs + (starts &&& oddBits) < bs then 1 else 0

end VbmSimd
