#!/usr/bin/env bash
# Writes corpus_random.v: N random goals (default 200, seed 42), with the
# random patterns of diff_random (random_gen.v).  Usage:
# select/tests/gen_random.sh [N [SEED]], the library being built.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
n=${1:-200}; seed=${2:-42}
cd "$root"
for s in diff_support random_gen; do rocq c -R . coq_tmp select/tests/$s.v; done
tmp=$(mktemp -d)
cat > "$tmp/gen.v" <<V
From coq_tmp.select.tests Require Import random_gen.
Elpi diff_random_goals $n $seed.
V
rocq c -R . coq_tmp "$tmp/gen.v" > "$tmp/out" 2>&1
{
  echo "(* Differential corpus: $n random goals (seed $seed), written by"
  echo "   gen_random.sh; each one gets 12 random patterns (random_gen.v). *)"
  echo "From Stdlib Require Import List."
  echo "From elpi Require Import elpi."
  echo "From coq_tmp.select.tests Require Import diff_support random_gen."
  echo "Import ListNotations."
  echo "Section Random."
  echo "Variables (f : nat -> nat -> nat) (g : nat -> nat)."
  echo
  grep -v "^\[\|^Warning\|^File" "$tmp/out"
  echo "End Random."
} > "$here/corpus_random.v"
rm -rf "$tmp"
