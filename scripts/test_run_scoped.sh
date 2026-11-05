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
# abort, on BOTH paths: the child records its pid, the wrapper is SIGTERMed (the pid started here), the child must die. The fallback always runs; the systemd path runs where a user manager works
# (where it does not, the fallback IS the path in use, and that is said, not skipped).
modes="fallback"
if systemctl --user is-system-running >/dev/null 2>&1 || [ "$(systemctl --user is-system-running 2>/dev/null)" = degraded ]; then modes="scope fallback"; else echo "test_run_scoped: no systemd user manager: the fallback path is the one in use"; fi
for mode in $modes; do
  if [ $mode = fallback ]; then export RUN_SCOPED_NO_SYSTEMD=1; else unset RUN_SCOPED_NO_SYSTEMD; fi
  rm -f "$tmp/pid" "$tmp/gpid"
  $rs abort 120 sh -c 'echo $$ > "$1"; sleep 100 & echo $! > "$2"; wait' sh "$tmp/pid" "$tmp/gpid" & w=$!
  for _ in $(seq 50); do [ -s "$tmp/gpid" ] && break; sleep 0.1; done
  [ -s "$tmp/gpid" ] || fail "$mode: the scoped child never started"
  c=$(cat "$tmp/pid"); g=$(cat "$tmp/gpid"); kill -0 "$c" || fail "$mode: the scoped child is not running"
  kill -TERM "$w"; wait "$w" || true
  for _ in $(seq 50); do kill -0 "$c" 2>/dev/null || kill -0 "$g" 2>/dev/null || break; sleep 0.1; done
  ! kill -0 "$c" 2>/dev/null || fail "$mode: an aborted run left its child alive (orphan)"
  ! kill -0 "$g" 2>/dev/null || fail "$mode: an aborted run left its grandchild alive (orphan)"
  ran_case
done
echo "test_run_scoped: ok (status, bound, abort reaped; paths: $modes)"; ran_done test_run_scoped
