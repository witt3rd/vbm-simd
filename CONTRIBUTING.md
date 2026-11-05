# Contributing

Thank you for looking. A short, honest note about how this repository works.

## Who lands changes

**Only the owner lands changes on `main`.** The repository lands directly, through a gate (`scripts/land-direct`, a pinned copy of [vbm-land](https://github.com/witt3rd/vbm-land)): no pull request is ever merged in the GitHub sense. That is the project's model (see [`AGENTS.md`](AGENTS.md)), not a lack of interest in your work.

**Outside contributions are welcome**: open an issue, or a pull request from a fork. The owner reads it, and if the change is accepted it lands through the lander as a commit (your authorship is kept where the change is applied as is; otherwise the commit says where it came from). A pull request is a proposal, and may be closed with the change landed separately.

## Pull requests and CI

- CI here runs only on a push to `main`, on a schedule and on manual dispatch, on GitHub-hosted runners with a read-only token and no secrets. It does not run on pull requests. A workflow that names `self-hosted` is refused by `scripts/lint-workflows.py` unless `.github/visibility` says `private`.
- Run the checks yourself: `mise install` then `mise exec -- scripts/tier1.sh` (the lints, the zero-warning build, the axiom gate, the spec-clause gate, the trust-ledger gate; about a minute). It is the same gate the lander runs. It needs `mise`, `git`, `bash`, `python3` with PyYAML and `curl`/`ca-certificates` (the Lean release brings its own C compiler). `scripts/tier2.sh` adds the independent proof checkers.

## What a good change looks like

- Small: at most about 150 changed production lines (`VbmSimd/`, `include/`), one idea per commit.
- Conventional Commits subjects (`feat(simd): ...`, `fix(shims): ...`, `docs: ...`).
- **A kernel lands with its clause, its machine and its theorem** (`docs/SPEC.md`, `VbmSimd/Spec.lean`, `VbmSimdProofs/`); no kernel without the theorem. A proof that is hard is decomposed, never weakened.
- Forbidden anywhere in Lean: `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `csimp`; no `bv_decide`, `native_decide` or `decide +kernel` (see `docs/findings/bv-decide.md` for why). Only the three standard axioms.
- Anything trusted (a C shim, a tool, a workflow) gets exactly one entry in `docs/trust-ledger.md` and, for a shim, a Lean model and a differential test.
- Gate-defining files (`scripts/`, `lakefile.lean`, the pins, the workflows, `docs/SPEC.md`, `docs/trust-ledger.md`, `AGENTS.md`) are the owner's: expect more discussion there.
- No private names, hosts or local paths anywhere (`scripts/lint.sh` refuses them).

## Licence

By submitting a contribution you agree that it is licensed under the Apache License 2.0, as the rest of the project (section 5 of the licence).

## Security

Report vulnerabilities privately: [SECURITY.md](SECURITY.md).
