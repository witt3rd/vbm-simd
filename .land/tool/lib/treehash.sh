# lib/treehash.sh: the tree hash of docs/pin.md section 1, defined ONCE. Sourced, never run.
# tree_hash DIR: print the SHA-256 of the sorted lines "<sha256 of the file> <path relative to DIR>" of every file under DIR except what is under .lake or .git.
# Returns 1, with the reason on stderr, for a missing DIR, a symlink or other non-regular file, or a path outside [A-Za-z0-9._+/-] (never a silently different hash).
tree_hash() (
  set -euo pipefail; export LC_ALL=C
  [ -d "${1:-}" ] || { echo "treehash: ${1:-} is not a directory" >&2; exit 1; }
  cd "$1"; files=()
  while IFS= read -r -d '' p; do
    [[ $p =~ ^\./[A-Za-z0-9._+/-]+$ ]] || { echo "treehash: $1: unsafe path ${p@Q}" >&2; exit 1; }
    { [ -f "$p" ] && [ ! -L "$p" ]; } || { echo "treehash: $1/${p#./} is not a regular file" >&2; exit 1; }
    files+=("$p")
  done < <(find . \( -path ./.lake -o -path ./.git \) -prune -o ! -type d -print0)
  if [ ${#files[@]} = 0 ]; then printf '' | sha256sum | cut -d' ' -f1; exit 0; fi
  printf '%s\0' "${files[@]}" | xargs -0 sha256sum -- | sed -E 's/^([0-9a-f]{64})  \.\//\1 /' | sort | sha256sum | cut -d' ' -f1
)

# export_commit REPO REV DEST: the exported tree of REV in REPO (git archive) into the existing directory DEST. The tree hash of a commit is tree_hash of this export (docs/pin.md section 1).
export_commit() { git -C "$1" archive --format=tar "$2" | tar -x -C "$3"; }
