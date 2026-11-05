# The specification: clauses

Each clause is a small sequential machine (`VbmSimd/Spec.lean`) that says what a word-parallel kernel must compute, one bit position at a time. A clause is **defined** where its machine is
written (its tag `[VS-n]` is in the doc comment) and **discharged** by a theorem whose docstring starts with the same tag. `scripts/spec-check.sh` (Tier 1) fails when a clause has no
definition or no theorem, or a tag is not a clause. Bit `i` is counted from the least significant bit; bytes of a block are read little-endian.

| clause | the machine | the kernel it specifies | discharged by |
|---|---|---|---|
| VS-1 | `scanXor x`: the state after bit `i` is the xor of bits `0 .. i` of `x` | `prefixXor`, `prefixXorC` (the in-string mask from a quote mask, with a carry across blocks) | `prefixXor_spec`, `prefixXorC_spec`, `prefixXorC_carry` (`VbmSimdProofs/PrefixXor.lean`) |
| VS-2 | `escSpec b pb`: byte `i` is escaped iff the byte before it is a backslash that is not itself escaped; `pb` is the carry in | `escaped`, `escOut` (the add-with-carry trick; the carry out of the block) | `escaped_spec`, `escOut_spec`, `quote_not_escaped_spec` (`VbmSimdProofs/Escape.lean`) |

Planned clauses (not in the tree yet; each lands with its proof): the byte-lane predicates (`eqLanes`, `pack8`), the UTF-8 validation automaton, the chunking theorem that threads a carry
state through consecutive blocks, `flatten` (the set bits of a mask as an index).

## What a clause does not say

A clause says what the kernel computes, not that it is fast and not that a C compiler or a CPU executes the Lean code as written: those are the trust ledger's (`docs/trust-ledger.md`).
