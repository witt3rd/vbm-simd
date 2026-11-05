#!/usr/bin/env bash
# Tier 1: scripts/lint-workflows.py passes the repo's workflows and FAILS on: `with:` under a `run:` step, a step with both/neither of uses/run, no jobs, a job with no steps, broken YAML, no trigger, a self-hosted runner (also behind an expression), the pull_request_target trigger, a secret other than GITHUB_TOKEN.
set -euo pipefail
export LC_ALL=C
cd "$(dirname "$0")/.."
python3 scripts/lint-workflows.py >/dev/null || { echo "test_lint_workflows: the repo's workflows are invalid" >&2; exit 1; }
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
neg() { # neg <name> <yaml>
  printf '%s\n' "$2" > "$T/$1.yml"
  if python3 scripts/lint-workflows.py "$T/$1.yml" >/dev/null 2>&1; then echo "test_lint_workflows: '$1' was accepted" >&2; exit 1; fi
}
head='name: x
on: push'
ok="$head
jobs:
  a:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
        with:
          fetch-depth: 0
      - run: true"
printf '%s\n' "$ok" > "$T/ok.yml"; python3 scripts/lint-workflows.py "$T/ok.yml" >/dev/null || { echo "test_lint_workflows: a valid workflow was rejected" >&2; exit 1; }
neg with-under-run "$head
jobs:
  a:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - run: true
        with:
          fetch-depth: 0"
neg inserted-step "$head
jobs:
  a:
    runs-on: ubuntu-latest
    steps:
      - name: free disk
        run: true
        with:
          fetch-depth: 0"
neg both "$head
jobs:
  a:
    runs-on: ubuntu-latest
    steps:
      - uses: x/y@v1
        run: true"
neg neither "$head
jobs:
  a:
    runs-on: ubuntu-latest
    steps:
      - name: nothing"
neg no-jobs "$head
jobs: {}"
neg no-jobs-key "$head"
neg no-steps "$head
jobs:
  a:
    runs-on: ubuntu-latest"
neg no-trigger "name: x
jobs:
  a:
    runs-on: ubuntu-latest
    steps:
      - run: true"
neg broken-yaml "$head
jobs:
  a: [unclosed"
neg self-hosted "$head
jobs:
  a:
    runs-on: [self-hosted, linux]
    steps:
      - run: true"
neg self-hosted-expression "$head
jobs:
  a:
    runs-on: \${{ inputs.x && 'ubuntu-latest' || fromJSON('[\"self-hosted\"]') }}
    steps:
      - run: true"
neg pull-request-target "name: x
on: pull_request_target
jobs:
  a:
    runs-on: ubuntu-latest
    steps:
      - run: true"
neg secret-use "$head
jobs:
  a:
    runs-on: ubuntu-latest
    steps:
      - run: echo \${{ secrets.DEPLOY_KEY }}"
echo "test_lint_workflows: ok (valid accepted; 13 invalid shapes each rejected)"
