#!/usr/bin/env bash
# Tier 1: the shared negative test of the ran-evidence class fix (docs/decisions/0002-ran-evidence.md). The defect: a negative self-test that passes when the thing under test never ran (a heavy-tool guard
# REFUSED `lake`; the zero-warning check saw a failure with no warning in it and called the gate clean). The class fix is that every gate and test prints `ran: NAME: N cases` (N > 0) and a refusal, skip
# or guard exit is a FAIL. Each shape is shown here to FAIL: a refused tool, a missing one, a timeout, a silent exit 0, a zero count, a SKIPPED line; and one clean case passes (the control of each).
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/lib-ran.sh
ev=$(pwd)/scripts/ran-evidence.sh; lib=$(pwd)/scripts/lib-ran.sh; zw=$(pwd)/scripts/check-zero-warning.sh
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
fail() { echo "test_ran_evidence: $*" >&2; exit 1; }
ok() { ran_case; }   # a case that held
# 1. the reader: scripts/ran-evidence.sh check
mklog() { printf '%b' "$2" > "$T/$1.log"; }
mklog good 'hello\nran: x: 7 cases\n'; "$ev" check good "$T/good.log" 2>/dev/null && ok || fail "check rejected a log with evidence"
mklog none 'hello\nok\n'; if "$ev" check none "$T/none.log" 2>"$T/e"; then fail "check passed a log with no ran line"; fi; grep -q 'no .ran: NAME: N cases. line' "$T/e" && ok || fail "check did not say why: $(cat "$T/e")"
mklog zero 'ran: x: 0 cases\n'; if "$ev" check zero "$T/zero.log" 2>/dev/null; then fail "check passed zero executed cases"; fi; ok
mklog skip 'x: SKIPPED: sometool was not found\nran: x: 3 cases\n'; if "$ev" check skip "$T/skip.log" 2>"$T/e"; then fail "check passed a SKIPPED check"; fi; grep -q SKIPPED "$T/e" && ok || fail "check did not name the skip"
mklog skipall 'x: SKIPPED: sometool was not found\n'; if "$ev" check skipall "$T/skipall.log" 2>/dev/null; then fail "check passed a wholly skipped script"; fi; ok
VBM_ALLOW_SKIP=1 "$ev" check skipall "$T/skipall.log" 2>"$T/e" && grep -q 'NOT RUN' "$T/e" && ok || fail "VBM_ALLOW_SKIP=1 did not allow (loudly) a wholly skipped script"
mklog garbled 'ran: x: many cases\nran:x: 3 cases\n'; if "$ev" check garbled "$T/garbled.log" 2>/dev/null; then fail "check passed a malformed evidence line"; fi; ok
# 2. the gate wrapper: scripts/ran-evidence.sh gate NAME REGEX CMD...
refuse() { echo "heavy: run this elsewhere or inside the capped slice." >&2; exit 126; }; export -f refuse
if "$ev" gate g 'n=([0-9]+)' bash -c refuse >/dev/null 2>"$T/e"; then fail "gate passed a command refused by a guard (exit 126)"; fi; grep -q 'exit 126' "$T/e" && ok || fail "gate did not report the refusal: $(cat "$T/e")"
if "$ev" gate g 'n=([0-9]+)' true >/dev/null 2>"$T/e"; then fail "gate passed a command that exited 0 and printed nothing (the vacuous pass)"; fi; grep -q 'no line matching' "$T/e" && ok || fail "gate did not say the count was missing"
if "$ev" gate g 'n=([0-9]+)' echo n=0 >/dev/null 2>&1; then fail "gate passed a count of zero"; fi; ok
[ "$("$ev" gate g 'n=([0-9]+)' echo n=5 2>&1 | tail -1)" = "ran: g: 5 cases" ] && ok || fail "gate did not print the evidence line for a command that ran"
# 3. must_fail (scripts/lib-ran.sh): the expected failure must be a real one; a refusal, a missing tool and a timeout are not
mf() {  # mf NAME EXPECT(0|1) -- the body of a command run under must_fail in its own shell; EXPECT 1 = the self-test must be FAILED by it
  local n=$1 want=$2 body=$3 rc=0
  printf '#!/usr/bin/env bash\nset -euo pipefail\n. %s\nmust_fail probe bash -c %q\nran_done probe\n' "$lib" "$body" > "$T/mf.sh"
  TMPDIR=$T bash "$T/mf.sh" >"$T/mf.out" 2>"$T/mf.err" || rc=$?
  if [ "$want" = 1 ]; then [ "$rc" != 0 ] && ! grep -q '^ran: probe' "$T/mf.out" && ok || fail "must_fail ($n): it passed (rc=$rc) but this is not a failure the self-test may count: $(cat "$T/mf.err")"
  else [ "$rc" = 0 ] && grep -q '^ran: probe: 1 cases' "$T/mf.out" && ok || fail "must_fail ($n): a real failure with a reason was not accepted (rc=$rc): $(cat "$T/mf.err")"; fi
}
mf "a real failure that says why" 0 'echo "the check failed: bad row" >&2; exit 1'
mf "the command succeeded" 1 'exit 0'
mf "silent failure" 1 'exit 1'
mf "refused by a guard (exit 126)" 1 'echo "heavy: run this elsewhere or inside the capped slice." >&2; exit 126'
mf "a refusal that exits 1 with the guard message" 1 'echo "heavy: run this elsewhere" >&2; exit 1'
mf "command not found (exit 127)" 1 'echo "no such tool" >&2; exit 127'
mf "a timeout (exit 124)" 1 'echo "timed out" >&2; exit 124'
# ran_done with no case is not a pass
if TMPDIR=$T bash -c ". '$lib'; ran_done empty" >/dev/null 2>&1; then fail "ran_done passed with no case executed"; fi; ok
# 4. the zero-warning check with `lake` REFUSED, missing, crashed or unable to fail: the exact defect. Stub lake first on PATH; the stub looks at the file it is given.
mkdir "$T/bin"
stub() { printf '#!/usr/bin/env bash\nf=${@: -1}\n%s\n' "$1" > "$T/bin/lake"; chmod +x "$T/bin/lake"; }
zwrun() { PATH="$T/bin:$PATH" "$zw" >"$T/zw.out" 2>"$T/zw.err"; }
stub 'echo "heavy: run this elsewhere or inside the capped slice." >&2; exit 126'
if zwrun; then fail "the zero-warning check passed with lake REFUSED by the heavy guard (the original defect)"; fi; ! grep -q '^ran:' "$T/zw.out" && ok || fail "the zero-warning check printed evidence with lake refused"
stub 'echo "segmentation fault" >&2; exit 139'
if zwrun; then fail "the zero-warning check passed with lake crashing"; fi; ok
stub 'exit 0'
if zwrun; then fail "the zero-warning check passed with a lake that cannot fail"; fi; ok
stub 'if grep -q "let y" "$f"; then echo "error: Variable name \`y\` is not explicitly referenced." >&2; exit 1; fi; exit 0'
zwrun && grep -q '^ran: zero-warning: 3 cases' "$T/zw.out" && ok || fail "the zero-warning check failed with a lake that behaves (the control): $(cat "$T/zw.err")"
ran_done test_ran_evidence
echo "test_ran_evidence: a refused, missing, skipped, silent or zero-count check FAILS in the reader, the gate wrapper, must_fail, the zero-warning check; the control of each passes"
