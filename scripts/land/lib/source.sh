#!/usr/bin/env bash
# Where the upstream copy of this tool lives, and how to look at it at one exact commit. Sourced, never run.
#   src_fetch SRC REF DEST   makes DEST a bare clone of SRC (OWNER/NAME on GitHub, via `gh`; or anything git can clone: a URL or a path) and prints the 40-hex commit REF names.
src_fetch() {
  local src=$1 ref=$2 dest=$3 c
  if [[ "$src" =~ ^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$ ]] && [ ! -e "$src" ]; then
    "${GH:-gh}" repo clone "$src" "$dest" -- --quiet --bare >/dev/null 2>&1 || { echo "cannot clone $src with gh" >&2; return 1; }
  else
    git clone -q --bare -- "$src" "$dest" >/dev/null 2>&1 || { echo "cannot clone $src" >&2; return 1; }
  fi
  c=$(git -C "$dest" rev-parse --verify -q "$ref^{commit}") || { echo "$src has no such tag or commit: $ref" >&2; return 1; }
  [[ "$c" =~ ^[0-9a-f]{40}$ ]] || return 1
  printf '%s\n' "$c"
}
