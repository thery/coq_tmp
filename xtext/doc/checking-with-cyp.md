[Back to the README of xtext](../README.md)

# Checking the texts with cyp

`sh cyprun.sh LIMIT name...` copies each text to `cyp-check/`, adds a
`flags:` line to its header (so that `Require Import XText.<file>`
finds the example files), and runs cyp's driver (`cyp/bin/cyp.ml`, which runs
`Cyp File` in the switch `elpi5`; `CYP_LIB` the directory where
`cyp/vernac/Cyp.v` is compiled), one text at a time, under `nice`, with
at most 8 GB of memory per text.  It prints, per text, the time and the
list items proved / not proved / not checked (`cyp-check/results.tsv`).

The 80 English texts written by default (staged translation), 300 s per
text (`cyp-check/results.tsv`, all rerun 2026-11-19, after 6.4.1 and
cyp's elimination step):

- all 80 texts are checked, in 176 s in all: 666 steps proved, 17 not
  proved, 504 not checked (lines with no claim: `Let`, `Assume`, the
  announcement of an induction, and the staged texts' "The element x
  belongs to T");
- none times out (`std_or_assoc` did, until cyp tried first whether a
  goal is one of its hypotheses: `tauto` runs for minutes on one of its
  goals, two hypotheses long);
- the 17 steps not proved are in 7 texts (`std_Nat_le_trans` 6,
  `half_le` 3, `std_Nat_lt_irrefl` 3, `std_rev_app_distr` 2, and 1 each
  in `drinker`, `std_length_rev`, `std_rev_involutive`); e.g. in
  `drinker`, "Applying not_all_ex_not to A, P and H, we have `exists n :
  A, ~ P n`";
- the texts that 6.4.1 changes (the motive left out) keep the statuses
  they had, with one step fewer each (the "In particular" that goes):
  cyp proves the closing step of the elimination, as `elim` would.

With the direct translation (`examples-direct/`, the default before;
`cyp-check/results_direct.tsv`): 72 texts checked in 595 s, 923 steps
proved, 23 not proved, 213 not checked, 5 timeouts (`half_le`,
`std_in_app_or`, `std_Nat_add_0_r`, `std_Nat_le_trans`, `std_or_assoc`).
The staged texts have fewer steps with a claim, more lines with no
claim, and fewer timeouts.

- cyp proves each claim again with its own tactics, so a green step says
  that the claim follows, not that it follows the way the text says.

The texts in the other languages (12 texts per language, 9 languages:
`fr it de nl ru zh ar ko la`), all 108 rerun 2026-11-19 on the staged
texts, 300 s per text (`cyp-check/results_langs.tsv`, one file for the 9
languages; it replaces `results_fr_it.tsv`; the checked texts in
`cyp-check/<lang>/`):

- all 108 texts are checked, none times out, in 21 to 26 s per language;
- each language gives 77 steps proved, 1 not proved, 38 not checked, as
  the same 12 texts in English;
- step by step, the roles and statuses in each `.cyp.json` are those of
  the English text, in all 108 texts: no step is proved in one language
  and not in another;
- the step not proved is the same in every language, in `drinker`:
  "Applying not_all_ex_not to A, P and H, we have `exists n : A, ~ P n`"
  (French "En appliquant not_all_ex_not à A, P et H, nous avons ...");
- the formulas are those of English too, except in `length_app_fix`,
  where two claims print the empty list `nil` in the other languages and
  `[]` in English (`length (nil ++ l2) = length (nil ++ l2)`), both proved.
