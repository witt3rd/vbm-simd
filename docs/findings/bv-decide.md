# Finding: `bv_decide` cannot be used where the axiom gate and the independent checkers are the standard

**Date and toolchain:** measured on Lean 4.35.0 (the pin in `lean-toolchain`).

**The obvious tool.** For fixed-width circuits (a prefix xor, an escape carry, a SWAR byte-lane test) Lean's `bv_decide` bit-blasts the goal and hands it to a SAT solver, then checks the certificate. It proves the statements
here in seconds, and a statement can be checked by it in a scratch file before a human-style proof is written.

**The constraint.** A theorem proved with `bv_decide` depends on one extra axiom per theorem (in `#print axioms`: `t._native.bv_decide.ax_1_5`, named after the theorem) because the certificate checker is run by the compiler's native evaluator (`ofReduceBool`-style trust).
Two consequences for a repository whose standard is "verified by construction, checked by independent kernels":

1. The axiom gate (`scripts/AxiomGate.lean`: every constant may depend only on `propext`, `Classical.choice`, `Quot.sound`) rejects it, by design.
2. The independent checkers (`leanchecker --fresh`, and nanoda over the exported proof) can only take the extra axiom on trust, so a `bv_decide` theorem is outside what they re-check. Raising `permitted_axioms` for it would be exactly the relaxation the gate exists to stop.

`decide +kernel` and `native_decide` have the same character (proof by evaluation in a trusted evaluator) and are banned by `scripts/lint-proof-eval.sh`.

**What was done instead.** The two non-lane-wise pieces were proved by hand (`VbmSimdProofs/PrefixXor.lean`, `VbmSimdProofs/Escape.lean`): an induction over the bit index with an invariant, whose step is a `decide` over 2^8 Boolean cases (kernel-checked, no evaluator trust, far below the proof-evaluation bound).
It is also the more informative proof: it states *why* the carry chain computes the right thing. `bv_decide` stays useful as a development-time oracle in a scratch file, to learn whether a statement is true before proving it.

**For the standard.** A VBM library that adopts "standard axioms only" should treat `bv_decide` as an oracle, not as a proof, and carry the machine-plus-invariant pattern (`docs/method.md`) for carry chains.
