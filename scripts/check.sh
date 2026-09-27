#!/usr/bin/env bash
# Rebuild from scratch, reject admits, and check the axioms of the main theorems.
set -uo pipefail
cd "$(dirname "$0")/.."

modules="DRRW Detectability Erasure transaction"
theorems="DR_RW DR_RW_main detectability crash_free_interleaving interleaving erasure transaction_atomic"

[ "${1:-}" = "--no-clean" ] ||
  find src \( -name '*.vo' -o -name '*.vos' -o -name '*.vok' -o -name '*.glob' \) -delete
make -j"$(nproc)" > /dev/null 2>&1 || { echo "build failed"; exit 1; }

status=0
for f in $(find src -name '*.v' | sort); do
  python3 scripts/strip_comments.py "$f" | grep -nwE 'admit|Admitted' | sed "s|^|$f:|" && status=1
done

tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
{ echo "From Memento Require Import $modules."
  for t in $theorems; do echo "Print Assumptions $t."; done
} > "$tmp/Axioms.v"
coqc $(grep -- '^-R' _CoqProject) "$tmp/Axioms.v" > "$tmp/out" 2>&1 || { cat "$tmp/out"; exit 1; }
grep -E '^[A-Za-z_][A-Za-z0-9_.]*( :|$)' "$tmp/out" | awk '{print $1}' | sort -u > "$tmp/axioms"
cat "$tmp/axioms"
grep -vE '(^|\.)(functional_extensionality_dep|propext|classic|constructive_indefinite_description)$' "$tmp/axioms" && status=1

[ "$status" = 0 ] && echo PASS || echo FAIL
exit "$status"
