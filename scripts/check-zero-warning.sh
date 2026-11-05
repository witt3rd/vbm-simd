#!/usr/bin/env bash
# The zero-warning gate and its negative self-test (docs/decisions/0002-ran-evidence.md). The build sets warningAsError (lakefile.lean); the mechanism is checked three ways, each of which
# has to HAVE RUN, not merely not-succeeded:
#   1. the option is set in lakefile.lean;
#   2. a file with a warning FAILS under -DwarningAsError=true, and its output carries the warning's own diagnostic ("not explicitly referenced"): a tool that was refused, missing or
#      crashed also "fails", with some other output (the defect of the first version of this check: a heavy-tool guard refused `lake`, the check saw a failure and called it clean);
#   3. a clean file PASSES under the same command (the control: the tool really runs here).
# Prints `ran: zero-warning: 3 cases` on success. Run from the repo root: scripts/check-zero-warning.sh.
set -euo pipefail
cd "$(dirname "$0")/.."
bad() { echo "check-zero-warning: $*" >&2; exit 1; }
grep -q 'warningAsError, true' lakefile.lean || bad "lakefile.lean does not set warningAsError"
st=$(mktemp "${TMPDIR:-/tmp}/zero-warning.XXXXXX.lean"); trap 'rm -f "$st"' EXIT
printf 'def f (x : Nat) : Nat :=\n  let y := 1\n  2\n' > "$st"
rc=0; wout=$(lake env lean -DwarningAsError=true "$st" 2>&1) || rc=$?
[ "$rc" != 0 ] || bad "a build with a warning succeeds under warningAsError (the zero-warning gate cannot fail)"
grep -q 'not explicitly referenced' <<<"$wout" || bad "the file with a warning failed (exit $rc), but not because of the warning, so the tool may never have run (a refusal, a missing tool): $wout"
printf 'def f (x : Nat) : Nat := x\n' > "$st"
cout=$(lake env lean -DwarningAsError=true "$st" 2>&1) || bad "a clean file fails under warningAsError (the control: the tool does not run here): $cout"
echo "tier1: zero-warning build: negative self-test ok (a file with a warning fails with the warning's diagnostic under warningAsError, a clean file passes)"
echo "ran: zero-warning: 3 cases"
