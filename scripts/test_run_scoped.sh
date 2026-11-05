#!/usr/bin/env bash
# Self-test of scripts/run-scoped.sh: exit status passes through, the bound holds (124), and an ABORTED run (the wrapper killed) leaves no live scope and no running child.
# The wrapper is signalled by the pid this script started itself; nothing is killed by pattern. The scope checks run only where a systemd user manager works.
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/lib-ran.sh   # ran_case / ran_done (docs/decisions/0005-ran-evidence.md)
rs=scripts/run-scoped.sh; fail() { echo "test_run_scoped: $*" >&2; exit 1; }
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
for mode in scope fallback; do
  if [ $mode = fallback ]; then export RUN_SCOPED_NO_SYSTEMD=1; fi
  [ "$($rs t 5 echo ok)" = ok ] && ran_case || fail "$mode: output lost"
  rc=0; $rs t 5 sh -c 'exit 7' || rc=$?; [ $rc = 7 ] && ran_case || fail "$mode: exit status not passed through ($rc)"
  rc=0; $rs t 1 sleep 30 || rc=$?; [ $rc = 124 ] && ran_case || fail "$mode: the bound did not hold ($rc)"
done
unset RUN_SCOPED_NO_SYSTEMD
rc=0; $rs 'b d' 5 true 2>/dev/null || rc=$?; [ $rc = 2 ] && ran_case || fail "a bad NAME was accepted"
[ "$($rs d 5 echo 'a$b $$ ${x}')" = 'a$b $$ ${x}' ] && ran_case || fail "a dollar in an argument was altered"
if systemctl --user is-system-running >/dev/null 2>&1 || [ "$(systemctl --user is-system-running 2>/dev/null)" = degraded ]; then
  # abort: the child records its pid, the wrapper is SIGTERMed (its own child pid, started here), the scope must be gone and the child dead
  $rs abort 120 sh -c 'echo $$ > "$1"; exec sleep 100' sh "$tmp/pid" & w=$!
  for _ in $(seq 50); do [ -s "$tmp/pid" ] && break; sleep 0.1; done
  [ -s "$tmp/pid" ] || fail "the scoped child never started"
  c=$(cat "$tmp/pid"); kill -0 "$c" || fail "the scoped child is not running"
  kill -TERM "$w"; wait "$w" || true
  for _ in $(seq 50); do kill -0 "$c" 2>/dev/null || break; sleep 0.1; done
  ! kill -0 "$c" 2>/dev/null || fail "an aborted run left its child alive (orphan)"
  ran_case
  echo "test_run_scoped: ok (status, bound, abort reaped; scope and fallback)"; ran_done test_run_scoped
else
  echo "test_run_scoped: ok (status, bound; no systemd user manager here: abort check SKIPPED)"; ran_done test_run_scoped
fi
