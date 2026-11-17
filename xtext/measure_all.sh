#!/bin/sh
# Regenerate every example with the mechanisms of XTEXT_OFF switched off;
# print one line per text: name, time, items, chars.
for v in paper lemmas inductive thesis stdlib elim_type; do sh measure.sh $v.v; done
timeout 1800 sh measure.sh exp_examples.v -Q /home/thery/git/libm-coremath-proofs/exp Exp
