[Back to the README of xtext](../README.md)

# Checking the texts with cyp

`sh cyprun.sh LIMIT name...` copies each text to `cyp-check/`, adds a
`flags:` line to its header (so that `Require Import XText.<file>`
finds the example files), and runs cyp's driver (`cyp/bin/cyp.ml`, which runs
`Cyp File` in the switch `elpi5`; `CYP_LIB` the directory where
`cyp/vernac/Cyp.v` is compiled), one text at a time, under `nice`, with
at most 8 GB of memory per text.  It prints, per text, the time and the
list items proved / not proved / not checked (`cyp-check/results.tsv`).
A list item is a node of the proof (the tree of the 2003 paper): its
mark is at the start of its text, and its closing paragraph, if any, is
part of it.  An item with no tag is a remark (▫️, not checked).

The 80 English texts written by default (staged translation), 300 s per
text (`cyp-check/results.tsv`, all rerun 2026-11-19, in the tree format):

| | nodes proved | not proved | remarks (▫️) | time |
|---|---|---|---|---|
| before the tree (`*by X*`, nodes without conclusion) | 666 | 17 | 504 not checked | 176 s |
| the tree (now) | 684 | 2 | 279 | 107 s |

- all 80 texts are checked, none times out;
- the 504 lines not checked before were the `Let` and `Assume` lines,
  the announcements of a proof by cases and the lines "The element x
  belongs to T".  The first three are now parts of real nodes (a `Let` or
  `Assume` line merged with its only sub-item or given a closing
  paragraph; an announcement is the opening of the node whose closing
  paragraph concludes the cases), and are checked.  The 279 remarks left
  are all "The element t belongs to `T`" lines on terms that are not
  variables (those on variables are left out);
- 16 of the 17 steps not proved before are proved now: in `drinker`,
  `std_length_rev`, `std_rev_app_distr` (2), `std_rev_involutive`,
  `std_Nat_lt_irrefl` (3), `std_Nat_le_trans` (6) and `half_le` (2 of 3), the
  steps "Applying L, we have C" name the lemma L as a justification now
  (`*Classical_Pred_Type.not_all_ex_not*{.just}`, `*List.rev_unit*{.just}`),
  and cyp applies it; before, L was plain text and the default tactics
  did not find it.  In `Trans_Inv` (proved before the tree, not with
  the first texts of the tree), the step whose conclusion is
  `Inv E R x z` (the steps before it prove `R z x`) is proved by cyp's last
  try on the goal unfolded (its weak head normal form);
- the 2 nodes not proved: in `half_le` (the one of the 17 still not proved), the node made of the binders of
  lia's internal proof and of its closing "Applying
  *ZMicromega.ZTautoChecker_sound*{.just}, ..." (not proved before either,
  as a separate step); in `std_Nat_le_trans`, a step of setoid rewriting
  "By application, we have `Morphisms.respectful iff iff (...)`, that is
  `forall x y : Prop, x <-> y -> ...`{.claim}": proved before, when its
  conclusion was the first form (an instance of the step above it); its
  conclusion is now the second form (decision 3), which unfolds
  `respectful` in a hypothesis, and the default tactics do not (a new
  failure, the one status that gets worse).

With the direct translation (`examples-direct/`, the default before;
`cyp-check/results_direct.tsv`, measured before the tree, not rerun): 72
texts checked in 595 s, 923 steps proved, 23 not proved, 213 not
checked, 5 timeouts.

- cyp proves each node again with its justifications, else its own
  tactics, so a green node says that the conclusion follows, not that it
  follows the way the text says.

The texts in the other languages (12 texts per language, 9 languages:
`fr it de nl ru zh ar ko la`), all 108 rerun 2026-11-19, 300 s per text
(`cyp-check/results_langs.tsv`; the checked texts in `cyp-check/<lang>/`):

- all 108 texts are checked, none times out, 141 s in all;
- each language gives 79 nodes proved, 0 not proved, 10 remarks, as the
  same 12 texts in English (before the tree: 77 proved, 1 not proved, 38
  not checked); text by text, the counts are those of English in all 108
  texts;
- the step not proved before, in `drinker` ("Applying not_all_ex_not to
  A, P and H"), is proved, as in English.
