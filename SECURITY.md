# Security policy

## Reporting a vulnerability

Please report a vulnerability **privately**: on the repository page open **Security**, then **Report a vulnerability** (GitHub private vulnerability reporting). Do not open a public issue or pull request for it.

Include what you found, the commit (or the pin you build) and a way to reproduce it. You will get an acknowledgement within a few days; a fix lands on `main` as a commit that says what was fixed.

## Supported versions

`main` only. The project is pre-release (no tags, no package registry): consumers pin a commit, and a fix is a new commit to pin.

## What counts

In scope:

- a kernel in `VbmSimd/` that computes something other than its specification in `docs/SPEC.md` (a counterexample to a proved theorem is a soundness bug, in Lean or in our statement of the clause);
- a trusted C shim in `include/vbm_simd.h` (`ld64`, `st64`, `st32`, `ctz`) that reads or writes outside its array, or differs from its Lean model in `VbmSimd/Shims.lean`;
- a gate that passes when it should fail (the gates are listed in `scripts/tier1.sh`; each has a negative self-test);
- a leak of a secret through the repository or its CI logs.

Out of scope: the Lean toolchain itself (report it to the Lean project; it is entry T01 of the trust ledger), and consumers' own code.

What is trusted and what is proved is written down in [`docs/trust-ledger.md`](docs/trust-ledger.md); read it before judging a report's impact.
