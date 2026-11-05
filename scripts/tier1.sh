#!/usr/bin/env bash
# Tier 1 (the pre-landing gate; scripts/land-direct runs it on the rebased combination): the vendored lander is intact, repository lints, forbidden constructs, the Init-only import rule,
# zero-warning build, the axiom gate, the spec-clause gate, the trust ledger. Every gate has a negative self-test and runs it here. Run from the repo root: mise exec -- scripts/tier1.sh.
set -euo pipefail
cd "$(dirname "$0")/.."
t0=$(date +%s)
scripts/land/bin/land-check
scripts/lint.sh
scripts/lint-pipefail.sh
scripts/lint-proof-eval.sh --selftest
scripts/test_lint_workflows.sh
python3 scripts/lint-workflows.py

# Lean sources under the roots that exist.
lean_sources() { find VbmSimd VbmSimdProofs -name '*.lean'; ls VbmSimd.lean VbmSimdProofs.lean; }

# 1. Forbidden constructs anywhere in Lean sources. Comments may mention them only on lines marked `-- tier1-allow`.
forbidden() { grep -HnE '\b(sorry|admit|axiom|unsafe|implemented_by|csimp)\b' "$@" | grep -v 'tier1-allow' || true; }
bad=$(forbidden $(lean_sources))
if [ -n "$bad" ]; then echo "tier1: forbidden construct(s):" >&2; echo "$bad" >&2; exit 1; fi
st=$(mktemp); trap 'rm -f "$st"' EXIT
for w in sorry admit axiom unsafe implemented_by csimp; do
  echo "theorem t : True := by $w" > "$st"; [ -n "$(forbidden "$st")" ] || { echo "tier1: the forbidden-constructs scan does not flag '$w'" >&2; exit 1; }
done
echo "-- a comment that says sorry -- tier1-allow" > "$st"; [ -z "$(forbidden "$st")" ] || { echo "tier1: the tier1-allow marker is not honoured" >&2; exit 1; }
echo "-- a comment that says sorry" > "$st"; [ -n "$(forbidden "$st")" ] || { echo "tier1: an unmarked comment is not flagged" >&2; exit 1; }
echo "tier1: forbidden-constructs scan: negative self-tests ok"

# 2. VbmSimd/ imports Init (implicitly) and other VbmSimd modules only: no Std, no Lean, no proofs (a consumer compiles this library into its own artifact).
bad_imports() { grep -HnE '^[[:space:]]*((public|meta|private)[[:space:]]+)*(import|prelude)\b' "$@" | grep -vE ':[0-9]+:import VbmSimd(\.[A-Za-z0-9_]+)*[[:space:]]*$' || true; }
bad=$(bad_imports $(find VbmSimd -name '*.lean') VbmSimd.lean)
if [ -n "$bad" ]; then echo "tier1: VbmSimd may import only VbmSimd modules (Init is implicit):" >&2; echo "$bad" >&2; exit 1; fi
for imp in 'import Lean' 'import Std.Data.HashMap' 'import VbmSimdProofs.Escape' 'prelude' 'public import Lean.Data.Json'; do
  printf '%s\n' "$imp" > "$st"; [ -n "$(bad_imports "$st")" ] || { echo "tier1: the Init-only import scan does not flag: $imp" >&2; exit 1; }
done
printf 'import VbmSimd.Spec\n' > "$st"; [ -z "$(bad_imports "$st")" ] || { echo "tier1: the Init-only import scan flags a VbmSimd import" >&2; exit 1; }
echo "tier1: Init-only import scan: negative self-tests ok"

# 3. Zero-warning build of both libraries (warningAsError is set in lakefile.lean); the mechanism is checked.
grep -q 'warningAsError, true' lakefile.lean || { echo "tier1: lakefile.lean does not set warningAsError" >&2; exit 1; }
printf 'def f (x : Nat) : Nat :=\n  let y := 1\n  2\n' > "$st"
if lake env lean -DwarningAsError=true "$st" >/dev/null 2>&1; then echo "tier1: a build with a warning succeeds under warningAsError (the zero-warning gate cannot fail)" >&2; exit 1; fi
echo "tier1: zero-warning build: negative self-test ok"
lake build VbmSimd VbmSimdProofs

# 4. The axiom gate: every constant of ours depends only on propext, Classical.choice, Quot.sound (--selftest: a non-standard axiom is rejected).
lake env lean --run scripts/AxiomGate.lean --selftest

# 5. The spec clauses, and the trust ledger (docs/trust-ledger.md).
scripts/spec-check.sh
scripts/trust-ledger-check.sh
echo "tier1: ok ($(( $(date +%s) - t0 )) s)"
