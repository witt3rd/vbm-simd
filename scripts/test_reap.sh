#!/usr/bin/env bash
# Self-test of scripts/lib-reap.sh and the abort traps built on it (test_native.sh / test_wasm.sh bgj): a script that is aborted (SIGTERM, set -e exit)
# while its background jobs run leaves none of them (nor their children) alive. The aborted script is signalled by the pid started here; nothing is killed by pattern.
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/lib-ran.sh
fail() { echo "test_reap: $*" >&2; exit 1; }
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
# the same construction as test_native.sh / test_wasm.sh: bgj with job control, reapj on EXIT, exit 143 on a signal
cat > "$tmp/victim.sh" <<'V'
set -euo pipefail
cd "$1"; . scripts/lib-reap.sh
jpids=(); bgj() { set -m; "$@" & jpids+=($!); set +m; }; reapj() { reap_pids "${jpids[@]}"; }
trap 'reapj' EXIT; trap 'exit 143' INT TERM HUP
bgj bash -c 'sleep 300 & echo $! > "$0.grand"; echo $$ > "$0.child"; wait' "$2/job"
[ "${3:-}" != fail ] || { sleep 1; exit 1; }
echo ready > "$2/ready"; bgj sleep 300; wait
V
root=$(pwd)
for how in term seterr; do
  rm -f "$tmp"/job.* "$tmp/ready"
  if [ $how = term ]; then bash "$tmp/victim.sh" "$root" "$tmp" & v=$!; for _ in $(seq 50); do [ -e "$tmp/ready" ] && break; sleep 0.1; done; [ -e "$tmp/ready" ] || fail "$how: the victim never started"
    kill -TERM "$v"; wait "$v" || true
  else bash "$tmp/victim.sh" "$root" "$tmp" fail || true; fi
  for f in child grand; do [ -s "$tmp/job.$f" ] || fail "$how: no $f pid recorded"; p=$(cat "$tmp/job.$f")
    for _ in $(seq 50); do kill -0 "$p" 2>/dev/null || break; sleep 0.1; done
    ! kill -0 "$p" 2>/dev/null || fail "$how: the background $f survived the abort (orphan)"; ran_case; done
done
# the check can fail: with the reaper trap removed the grandchild survives (then it is stopped here by its recorded pid)
sed 's/^trap .reapj. EXIT; //' "$tmp/victim.sh" > "$tmp/noreap.sh"; rm -f "$tmp"/job.* "$tmp/ready"
bash "$tmp/noreap.sh" "$root" "$tmp" fail || true
sleep 0.3; g=$(cat "$tmp/job.grand"); if kill -0 "$g" 2>/dev/null; then kill "$g"; ran_case; else fail "self-test: without the reaper the job did not survive (the check cannot fail)"; fi
ran_done test_reap
