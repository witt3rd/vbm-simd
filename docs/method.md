# The method: proving a word-parallel kernel against a one-bit-at-a-time machine

**The class.** *Block-parallel evaluation of a finite-state transducer with a small carry state* (a chunked parallel scan). The specification is a sequential machine over bits or bytes with a handful of state bits
(inside an escape, inside a string, previous byte was part of a token, UTF-8 continuation owed). The fast code consumes 64 bytes per step, computes all 64 outputs at once from per-lane predicates and a few carry-propagating
primitives (a 64-bit addition for escapes, a prefix xor for string parity), and hands a few bits of state to the next block. Every vectorised scanner of text is an instance.

**The five steps** (each lands as its own change; steps 1, 2 are done here for two primitives):

1. *Specification.* The Mealy machine, as a Lean function over `Nat` positions (`VbmSimd/Spec.lean`: `scanXor`, `escSpec`). It is the definition of correct; it is small enough to read. It carries a clause tag `[VS-n]` (`docs/SPEC.md`).
2. *Lane theorem.* A carry-propagating primitive is a sequential machine in disguise (an adder's carry chain is the machine's state). Prove, by induction on the bit index, an invariant `Inv` that relates the primitive's carry at bit `i` to the
   machine's state at byte `i`; the induction step is a statement about a handful of Booleans, discharged by `decide` (256 cases for the escape trick: `inv_step`). Lane-wise primitives (compare, and, or, xor) need no induction: bit `i` of the result is a function of byte `i`.
   A doubling cascade (the prefix xor) is proved by a window lemma: the xor over the `w` bits ending at `i` splits at any point, so each shift-xor step doubles the window (`xw_add`, `step`).
3. *Block theorem.* For every entry state and every 64-byte block, the kernel returns the machine's state after the block and, at every bit, the machine's output.
4. *Chunking theorem* (generic, proved once). If a block function computes the machine's state and outputs for one block, iterating it over consecutive blocks computes them for the concatenation. By induction on the number of blocks.
5. *Composition.* The escape machine feeds the string machine feeds the scalar machine; a composed kernel is the composed machine (the output mask of one is the input mask of the next), and the product state is the tuple.

**What the proofs state.** About `UInt64` code. The bridge to `BitVec` (where the library lemmas live) is `simp` with the `UInt64.toBitVec_*` lemmas: `prefixXor_toBitVec`, `escaped_toBitVec`.

**A restriction worth knowing.** The escape kernel is specified only at bytes that are not themselves backslashes: it does not mark the escaped backslashes inside a run, and the one consumer (`quote and not escaped`) never asks about a backslash
(`quote_not_escaped_spec` states exactly the consumer's use, with the hypothesis that the quote and backslash masks are disjoint). Stating less than the machine says, and exactly what is used, keeps the proof small.

**Tools used and not used.** Standard axioms only. `bv_decide` is excluded (`docs/findings/bv-decide.md`); `decide +kernel` and `native_decide` are excluded (see AGENTS.md)
(restate through a shallow lemma instead of evaluating a big constant).
