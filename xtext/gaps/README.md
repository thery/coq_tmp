# The conditions cyp leaves open in xtext's texts, and cyp's bounded searches

Two tactics of cyp ([../../cyp/vernac/Gaps.v](../../cyp/vernac/Gaps.v))
were chosen by the measurements of this directory:

- `cyp_gap`, the coarse gap tactic, tried on a condition that the step's
  justification, the rules and the default tactics leave open;
- `bounded_firstorder`, what cyp runs for `firstorder` (in a `by:` line or
  a justification `*firstorder*{.just}`): `firstorder` has no bound, and was the cause of
  most of the timeouts and memory blow-ups of xtext's texts.

The measurements below (2026-11-18) were made on the texts written
before the tree of the 2003 paper, in the old form (`*by X*`, several
claims per step); they were not rerun.  cyp's results on today's texts
are in [../doc/checking-with-cyp.md](../doc/checking-with-cyp.md).

Both are bounded searches with no time limit: the goal unfolded and
introduced, its conjunctions split, the connectives of the hypotheses taken
apart (each step removes one), then `eauto 4` or `congruence` (and again
after `simpl`); `cyp_gap` also tries a case analysis on the booleans, an
induction on a binder of the goal, a case analysis on a variable, a
constructor.

## The scripts

- `make_mode.sh CONTRACTION ANNOTATION OUTDIR`: all the English texts of
  xtext written with one setting of `XTEXT_CONTRACTION` and
  `XTEXT_ANNOTATION`, from a copy of `xtext/` (nothing here is touched);
- `probe.sh LIMIT OUTDIR text.md...`: each text checked by `Cyp File` with
  a Proof block, one text at a time, under `nice`, with a time limit per
  text (LIMIT, a guard of the run only: see "No time limit" below) and at most `CYP_MEMORY_GB` (default 8) GB of memory; it prints the
  time, the conditions and the maximum memory of each text.  On each
  condition left open (every condition with `BARE=1`) it runs the Ltac
  `PROBE` of `Probe.v`: `gap_probe` (the candidates for `cyp_gap`),
  `gap_final` (`cyp_gap` alone), `fo_probe` and `fo2_probe` (bounded
  searches), `idtac` (nothing: the conditions cyp leaves).  Each candidate
  must close the goal, with no time limit (see "No time limit" below).
  `CYP_LIB` is the cyp library used;
- `table.sh OUTDIR/*.log`: one line per condition and candidate (text,
  condition, candidate, OK or KO, seconds); Ltac cannot read the name of a
  goal (`?c2a`), so the k-th probed goal is the k-th condition that cyp
  lists (its lines 🔶), the goals being in the order of the text;
- `order.sh TABLE`: the candidates in a greedy order (each the one that
  closes most of the conditions still open); `order.sh TABLE tac...`: the
  conditions closed by that order and the time per condition.

## The test sets (2026-11-18)

The 77 English texts of `examples/` (the private ones excluded), written
in two modes: default (`guarded`, `all`: the texts of `examples/`) and
maximal (`XTEXT_CONTRACTION=maximal`, `XTEXT_ANNOTATION=thesis`).  xtext
writes in each header `by: tauto | congruence | lia | firstorder | auto`;
each mode is also checked with that line removed (cyp's own default
tactics only, `tauto`, `lia`, `nia`, `lra`), which leaves many more
conditions open.

The conditions left open by cyp before this work (`firstorder`
unbounded, no gap tactic):

| set | conditions left open | texts with no result |
|---|---|---|
| default | 22 | 6 |
| maximal | 22 | 6 |
| default, no `by:` | 214 | 2 |
| maximal, no `by:` | 178 | 3 |

With `by:`, the texts with no result are `half_le` and `std_in_app_or`
(over 8 GB), `std_Nat_add_0_r`, `std_Nat_add_succ_r`, `std_Nat_le_trans`
and `std_or_assoc` (over 300 s).  Without it, `std_in_app_or` (and
`half_le` in the maximal mode) still go over 8 GB and `std_or_assoc` over
300 s.

Maximal contraction gives no more open conditions than the default: the
steps it removes are application steps that `firstorder` or `auto` (with
`by:`), or `eauto` (without), still close.  Without `by:` it gives fewer,
because it writes fewer steps.

With `by:` the 22 conditions are the same in both modes: 13 closing steps
of a case analysis on booleans (`std_andb_comm`, `std_negb_andb`, ...; no
justification, since `destruct` is tactic code), 3 steps `*by ex_intro*`
(cyp applies `ex_intro` and cannot find the witness), 4 closing steps of a
`list_ind` induction whose two cases are claims, and the two closing steps
of `length_app_fix` (a `fix` and a `match`).  Without `by:`, most are
application steps that a proof search closes from the claims before them
(`eauto`: 179 of 214 in the default set, 137 of 178 in the maximal one).

## firstorder and its bounded replacement

On every condition of the texts with `by:` (`BARE=1`, `fo_probe`,
`fo2_probe`; default mode, 1283 conditions):

| tactic | closes | of the 1040 that firstorder closes | total time | slowest |
|---|---|---|---|---|
| `firstorder` | 1040 | 1040 | 294 s | over 2 s |
| decomposition, then `eauto 4` | 942 | 915 | 2.2 s | 0.22 s |
| `eauto 4` | 898 | 829 | 1.1 s | 0.17 s |
| `dintuition (eauto 3)` | 953 | 894 | 37 s | over 2 s |
| `intuition (eauto 3)` | 917 | 852 | 37 s | over 2 s |

The maximal mode gives the same picture (932, 814, 742, 796, 749 of the
1127 conditions).  `intuition` and `tauto` are not bounded either.  Most
of the conditions that only `firstorder` closes are the statements of the
lemmas a step uses (*Using lt_eq_cases we get ...*), which cyp closes by
the lemma itself, and setoid steps (`Basics.impl`, `Morphisms.Proper`).

In cyp, with `cyp_firstorder := bounded_firstorder` and no gap tactic
(texts with `by:`):

| set | before: open, no result, total time | after: open, no result, total time |
|---|---|---|
| default | 22, 6 texts, 2013 s | 23, 2 texts, 758 s |
| maximal | 22, 6 texts, 2109 s | 20, 3 texts, 883 s |

No condition that `firstorder` closed is left open; the 3 `*by ex_intro*`
steps are now closed (the bounded search finds the witness);
`std_Nat_add_0_r`, `std_Nat_add_succ_r`, `std_Nat_le_trans` (and `half_le`
in the default mode) now finish, with 4 (resp. 1) open conditions of
their own.  What still goes over 8 GB (`std_in_app_or`, and `half_le` in
the maximal mode) or 300 s (`std_or_assoc`) is not `firstorder`: in
`std_in_app_or` it is the step *by list_ind* (condition 4), the search of
cyp's rules over the premises of `list_ind`.

## cyp_gap on the open conditions

On the conditions left open by cyp before this work (`gap_final`):

| set | closed | time when closed (mean / max) | time when not (mean / max) |
|---|---|---|---|
| default | 22 of 22 | 0.05 s / 0.13 s | - |
| maximal | 22 of 22 | 0.05 s / 0.11 s | - |
| default, no `by:` | 211 of 214 (98.6%) | 0.008 s / 0.16 s | 0.04 s / 0.06 s |
| maximal, no `by:` | 177 of 178 (99.4%) | 0.008 s / 0.12 s | 0.05 s / 0.05 s |

The order of the ways follows `order.sh` (no `by:`, default set: a case
analysis then a proof search 192, a proof search +9, an induction on a
binder +5, the decomposition +4, the booleans +3), with the cheap ways
first.  The conditions left: `half_le` 1, `forall n0, n0 / 2 <= n0` from
its sub-steps, which needs the lemma of strong induction the text names;
its 1.1.1.1.9.2.1.6 and .7, the certificates of a `lia` proof
(`Tauto.eval_bf ...`); and `std_Nat_le_trans` 8, `Basics.impl (n <= m)
(m <= p -> n <= p)`, which needs `lia` after the unfolding.

## cyp with both (the library of this branch)

All 77 texts of each set checked by cyp with `bounded_firstorder` and
`cyp_gap` (`PROBE=idtac`):

| set | before: open, no result | now: open, no result | total time now |
|---|---|---|---|
| default | 22, 6 texts | 4, 2 texts | 780 s (2013 s before) |
| maximal | 22, 6 texts | 1, 3 texts | 921 s (2109 s before) |
| default, no `by:` | 214, 2 texts | 5, 2 texts | 704 s |
| maximal, no `by:` | 178, 3 texts | 1, 3 texts | 864 s |

The open conditions are those of the end of the section above, in the
texts that now finish (`half_le`, `std_Nat_le_trans`).  On cyp's own
examples and demos (`cyp/gaps_regress.sh`) the results are the same, and
the times too (33.1 s before, 33.4 s now for the same files, within the
noise of a run).

## No time limit (2026-11-23)

`Probe.v` has no time limit any more (it had `timeout 2` on each
candidate).  Each candidate is now the bounded version that cyp and
xtext run: `tauto` is `itauto auto` (and `intuition t` is `itauto t`),
`firstorder` is `bounded_firstorder`, `typeclasses eauto` has depth 5,
the rewriting with the hypotheses is done at most 5 times
(`rewrite_steps`; at 20 the terms of `even_or_odd` grew past 7 GB), the
local unbounded `decompose_all` is replaced by the bounded one of
`../../prooftext/Tactics.v`, and `lia`, `nia` run behind `lia_guard`.
Three candidates are gone, as they have no bounded version: `solve_proper`
(its rewriting runs a search for instances with no bound; it closed 152
conditions, each also closed by another candidate),
`dintuition (eauto 3)` (`itauto (eauto 3)` is there), and `fo_diff` (the
goals that `firstorder` closes and the bounded search does not: it needs
`firstorder` itself, with a time limit).  The measurements of `firstorder`
above were made with the time limit, and are not rerun.

On the 80 English texts (`BARE=1`, every condition, 738), each candidate
closes as many conditions as before, except: `tauto` 466 → 581, `firstorder`
631 → 656, `simpl_firstorder` 631 → 647, `induction_firstorder` 92 → 101
(the bounded versions, with no limit of 2 s, close more), `rewrite_hyps`
528 → 538, and `solve_proper` (152) is gone.  The whole probe takes 176 s
(325 s with the time limits), the slowest text 10 s.  `gap_probe`,
`fo_probe`, `fo2_probe` and `gap_final` run on all 80 texts, none stopped
by the time limit of the run (900 s).

### lia_guard

`lia` and `nia` have no bound in Rocq 9.1.  `lia_guard`
(`../../prooftext/Tactics.v`) is a check of the goal's shape before them,
with no search: it counts the case splits that `lia` may make (each
disjunction, equivalence, negation, implication inside a hypothesis; in
the goal, a conjunction or an equality; each `-`, `pred`, `max`, `min`,
`abs`, `div`, `mod`, ...) and the hypotheses that are propositions, and
refuses above 50 case splits or 16 hypotheses ("lia_guard: N case
splits, at most 50").  `lia_stats` prints the two counts.  Measured on
every call of `lia` and `nia` (with the counts printed, then whether the
call succeeded):

| calls of | calls | succeeded | largest success: splits, hypotheses | largest failure: splits, hypotheses |
|---|---|---|---|---|
| xtext, default texts (`xtext_lia`) | 38 | 6 | 6, 3 | 7, 3 |
| xtext, direct translation (`xtext_lia`, `xtext_g_lia`) | 44 | 20 | 19, 3 | 36, 4 |
| cyp on the 188 texts (English and languages) | 357 | 8 | 28, 6 | 42, 8 |
| cyp on its examples (`cyp/gaps_regress.sh`) | 220 | 128 | 7, 8 | 4, 5 |
| the probe (`t_lia`, `t_nia`, `t_simpl_lia`, `BARE=1`) | 2214 | 677 | 34, 7 | 34, 9 |

The bounds are the largest successes, 34 splits and 8 hypotheses, times
about 1.5 and 2.  No call measured is refused: cyp's results on its
examples and on xtext's texts, xtext's texts and the probe's counts are
the same with the guard (and cyp's `cyp_lia`, `cyp_nia` now run
`guarded_lia`, `guarded_nia`).  The guard bounds what `lia` is given, not
its search: a goal under the bounds may still be hard; none of the
measured calls ran away.  So the time limit of a whole run (`LIMIT` of
`probe.sh` and `cyprun.sh`, `timeout 300` of `cyp/gaps_regress.sh`) is
kept, as a guard of the run: it changes no result of a run that finishes.
