#!/usr/bin/env bash
# scripts/run-scoped.sh NAME MAXSEC CMD...: run a long runner (the list: scripts/long-runners.txt) in a transient systemd user scope with
# RuntimeMaxSec=MAXSEC, so an aborted run (the caller killed, a SIGKILL included, a terminal gone) cannot leave the runner or its children orphaned:
# the scope is stopped on exit, on a signal and, if even this wrapper dies, by RuntimeMaxSec. Exit status = the command's (124 on the bound).
# Standing rule: nobody kills by a derived pid or a pattern; this helper stops only its own scope, by the unit name it chose.
# Without a usable systemd user manager (hosted CI) it falls back to `timeout` in its own process group: the bound still holds.
# scripts/lint-scoped-runners.sh (Tier 1) fails any script that runs a listed runner without going through here.
set -uo pipefail
# internal: the scoped side. The arguments travel in a NUL-delimited file, because systemd-run's treatment of $ in its own arguments differs between versions.
if [ "${1:-}" = --exec-argfile ]; then mapfile -d '' -t cmd < "$2"; rm -f "$2"; exec "${cmd[@]}"; fi
[ $# -ge 3 ] || { echo "usage: run-scoped.sh NAME MAXSEC CMD..." >&2; exit 2; }
name=$1; max=$2; shift 2
case $name in *[!A-Za-z0-9_-]*|'') echo "run-scoped: bad NAME: $name" >&2; exit 2;; esac
case $max in *[!0-9]*|'') echo "run-scoped: bad MAXSEC: $max" >&2; exit 2;; esac
usable=1
command -v systemd-run >/dev/null 2>&1 || usable=0
systemctl --user is-system-running >/dev/null 2>&1 || [ "$(systemctl --user is-system-running 2>/dev/null)" = degraded ] || usable=0
[ -z "${RUN_SCOPED_NO_SYSTEMD:-}" ] || usable=0   # test hook: force the fallback
if [ $usable = 0 ]; then exec timeout --kill-after=10 "$max" "$@"; fi
unit="vbm-$name-$$-$RANDOM"
stop() { systemctl --user stop "$unit.scope" >/dev/null 2>&1 || true; }
trap 'stop; rm -f "${argf:-}"' EXIT
trap 'stop; exit 143' INT TERM HUP
argf=$(mktemp); printf '%s\0' "$@" > "$argf"
systemd-run --user --scope --quiet --collect --unit="$unit" -p RuntimeMaxSec="$max" -- "$(readlink -f "$0")" --exec-argfile "$argf" &
wait $!; rc=$?
# a scope that hit RuntimeMaxSec is killed by SIGTERM: report it the way timeout does
[ $rc -ne 143 ] || rc=124
exit $rc
