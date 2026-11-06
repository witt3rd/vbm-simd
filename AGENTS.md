# AGENTS.md: vbm-simd

Verified bit-parallel kernels, written once in Lean: the model of the vector operations a word-at-a-time (SWAR) or SIMD implementation uses, the kernels built from them (prefix xor,
escape carry, byte-lane classification, UTF-8 validation), their proofs against one-bit-at-a-time machines, and the small trusted C shims that let the compiler reach the hardware. Built for
[vbm-json](https://github.com/witt3rd/vbm-json) (its structural stage) and meant to be reused by any VBM (verified bare metal) library that scans text. Agent-built, no human code review. Standard:
`VbmSimd` is the library (Lean namespace `VbmSimd`, `Init` only), `VbmSimdProofs` the proofs (never linked). The specification is `docs/SPEC.md` (clauses `VS-n`, checked by Tier 1); the unverified
base is `docs/trust-ledger.md`. `README.md` is the public face (kept short); `docs/method.md` is the proof pattern.

## Status
Landed: `VbmSimd/Spec.lean` (the machines), `PrefixXor.lean`, `Escape.lean`, `Lanes.lean` and their proofs (clauses VS-1 to VS-4); `Shims.lean` with `include/vbm_simd.h` (VS-5, VS-6, ledger T10); `Cursor.lean` (VS-7); `mask8`/`eqMask64` in `Lanes.lean` (VS-8). Planned, one landing each: the chunking theorem,
UTF-8 validation, then the vector-ISA shims (each its own ledger entry). Toolchain: Lean 4.35.0 pinned in `mise.toml` and `lean-toolchain`
(no elan). Run everything as `mise exec -- ...`; the gate is `mise exec -- scripts/tier1.sh`.

## Hard rules
- **Forbidden anywhere in Lean:** `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `csimp` (Tier 1 scans for them; a comment may mention one only on a line marked `tier1-allow`). A proof is hard? Decompose it; never weaken the statement.
- **No `bv_decide`, no `native_decide`, no `decide +kernel`:** the first adds an axiom per theorem that the axiom gate rejects and the independent checkers can only take on trust; the others are proof by evaluation. Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`: `scripts/AxiomGate.lean`).
- **Spec first.** A kernel lands with its clause in `docs/SPEC.md`, its machine in `VbmSimd/Spec.lean` and its theorem; no kernel without the theorem. No unproved claim called verified.
- **The shims decide nothing.** A C shim moves or counts bytes and bits (a load, a store, a count of trailing zeros); every shim has a Lean model, a differential test against it and ONE trust-ledger entry; a vector-ISA shim is selected at build time and the portable path is always available.
- **`VbmSimd` imports `Init` and other `VbmSimd` modules only** (Tier 1 scans the imports). `VbmSimdProofs` may import `Std` and `Lean`; nothing in `VbmSimd` may import it.
- **No secrets, no internal names, no local paths** in the repository (public). No paid model calls from a test or a gate.

## Landing (direct to main, no PRs)
- Work in a worktree off a fresh origin/main. Keep changes small; at most 45 min without a passing build: stop and write a decomposition plan.
- Commit locally with Conventional Commits. Land only with `scripts/land-direct`; never push main yourself, never force-push it, never open a PR.
- Main is RED when the Tier 1 job of its latest push failed. While red or frozen, only a fix or revert lands. Never hotfix on main: pull the revert, reproduce in a new worktree, resubmit.
- `scripts/land/` and `scripts/land-direct` are a pinned copy of vbm-land: never edit them (`scripts/land/bin/land-check` fails the gate). Change the tool upstream, then `scripts/land/bin/land-update <tag>`.
- Anything in the repository may be edited and landed like any change (spec, proofs, code, scripts, docs, this file); only the lander files and the signing keys are off limits. Do not weaken a check to make it pass.
- Decide anything reversible and log it. Escalate only money, data loss, secrets, publishing, or harm to a third party; say so in one line and stop.

## Layout
`VbmSimd/` the library (`Spec.lean` the machines; one module per kernel) · `VbmSimdProofs/` the proofs · `include/` the trusted C header · `tests/` the shim test · `scripts/` the gates (`land/` is vendored) · `docs/` spec, trust ledger, decisions, method, findings.
