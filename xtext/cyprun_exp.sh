#!/bin/sh
# cyp on the CORE-MATH texts, with the libraries of the exp proof added to
# the header of the copy (the header written by xtext only requires the
# file of the theorem, which does not import its own dependencies).
# usage: sh cyprun_exp.sh LIMIT name...
lim=$1; shift
cd cyp-check
for f in "$@"; do
  sed 's|^require: .*|require: From Stdlib Require Import ZArith Reals Lia. From Flocq Require Import Core BinarySingleNaN. From Exp Require Import Common Algorithm Rnd Branch1. Open Scope R_scope.|' ../examples/$f.md > $f.md
  rm -f $f.checked.md
  s=$(date +%s)
  CYP_ROCQ="rocq c -R /home/thery/git/coq_tmp/xtext XText -Q /home/thery/git/libm-coremath-proofs/exp Exp" timeout $lim \
    opam exec --root=/home/thery/opam-rocq.9.1.0 --switch=native -- \
    /home/thery/git/coq_tmp/cyp/_build/default/bin/cyp.exe $f.md >/dev/null 2>&1
  t=$(( $(date +%s) - s ))
  g=$f.checked.md
  if [ -f $g ]; then
    printf "%s\t%s\t%s\t%s\t%s\n" $f $t $(grep -c '^ *- ✅' $g) $(grep -c '^ *- ❌' $g) $(grep -c '^ *- ▫️' $g)
  else
    printf "%s\t%s\ttimeout\n" $f $t
  fi
done
