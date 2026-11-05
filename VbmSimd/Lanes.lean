import VbmSimd.Spec
/-! # `VbmSimd.Lanes`: byte-lane predicates on a 64-bit word (SWAR), and the packing of their flags into a bit mask

Eight bytes sit in one `UInt64`. `eqLanes c w` compares all eight at once and flags each lane that matches in the top bit of the lane (`0x80`); `pack8` gathers the eight flags into the low eight bits of a word,
lane `k` to bit `k`, with one multiply. The classification of a 64-byte block into bit masks is eight words through these two functions and an `or`/shift per word.
Proved: `VbmSimdProofs.Lanes` (`[VS-3]` `eqLanes`, `[VS-4]` `pack8`).

Write byte-lane constants as literals at the call site (`eqLanes 0x2222222222222222 w`), never as a computed `rep c`: a closed term built from a function is initialised once at start-up and read from memory by the
C code Lean emits, not folded to an immediate (measured). -/
namespace VbmSimd

/-- `0x7f` in every lane. -/
@[inline] def lo7 : UInt64 := 0x7f7f7f7f7f7f7f7f

/-- `0x80` in each byte lane of `x` that is zero and `0x00` in every other bit: `~(((x & 0x7f..) + 0x7f..) | x | 0x7f..)`. Exact: no lane's addition carries into its neighbour
(`(x & 0x7f) + 0x7f` is at most `0xfe`), so the top bit of the sum is set iff the low seven bits are not all zero, and `x` itself supplies the top bit. -/
@[inline] def zeroLanes (x : UInt64) : UInt64 := ~~~(((x &&& lo7) + lo7) ||| x ||| lo7)

/-- `0x80` in each byte lane where `w` and `c` agree, `0x00` elsewhere (`eqLanes_spec`, `[VS-3]`). -/
@[inline] def eqLanes (c w : UInt64) : UInt64 := zeroLanes (w ^^^ c)

/-- The eight lane flags of `m` (one per lane, in the top bit of the lane, all other bits zero) packed to the low eight bits: lane `k` to bit `k`, nothing above bit 7
(`pack8_spec`, `[VS-4]`). The multiply puts bit `8k` at bit `56 + k`; no two partial products meet, so no carry. -/
@[inline] def pack8 (m : UInt64) : UInt64 := ((m >>> 7) * 0x0102040810204080) >>> 56

/-- Word `k` of a block given as eight words (`w7` for any `k ≥ 7`): the way the specs of the block masks name the eight words. -/
def blockWord (w0 w1 w2 w3 w4 w5 w6 w7 : UInt64) (k : Nat) : UInt64 :=
  match k with | 0 => w0 | 1 => w1 | 2 => w2 | 3 => w3 | 4 => w4 | 5 => w5 | 6 => w6 | _ => w7

/-- The mask of a 64-byte block (eight words) from a per-word function `f` that puts the eight bits of one word in its low byte: word `k` supplies bits `8k .. 8k+7` (`mask8_bit`, `[VS-8]`). -/
@[inline] def mask8 (f : UInt64 → UInt64) (w0 w1 w2 w3 w4 w5 w6 w7 : UInt64) : UInt64 :=
  f w0 ||| (f w1 <<< 8) ||| (f w2 <<< 16) ||| (f w3 <<< 24) ||| (f w4 <<< 32) ||| (f w5 <<< 40) ||| (f w6 <<< 48) ||| (f w7 <<< 56)

/-- The mask of the bytes of a 64-byte block (eight words) equal to the byte `c` repeated in all lanes of `c` (a literal such as `0x2222222222222222`): bit `p` is set iff byte `p` of the block is that byte
(`eqMask64_spec`, `[VS-8]`). -/
@[inline] def eqMask64 (c w0 w1 w2 w3 w4 w5 w6 w7 : UInt64) : UInt64 := mask8 (fun w => pack8 (eqLanes c w)) w0 w1 w2 w3 w4 w5 w6 w7

end VbmSimd
