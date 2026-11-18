#!/bin/sh
# Regenerate every example with the mechanisms of XTEXT_OFF switched off;
# print one line per text: name, time, items, chars.
for v in paper lemmas inductive thesis stdlib elim_type; do sh measure.sh $v.v; done
