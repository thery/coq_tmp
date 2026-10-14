(* Roots of negative numbers through roots of unity (milestone M9): the     *)
(* decision lemmas of the neg mode, for a posroot with a negroot (PosRoot.v):*)
(*   w : negroot r  gives  w n ^+ n = -1  and, for 0 <= a,                  *)
(*                  proot r n (- a) = proot r n a * w n                      *)
(*                  (so w n = proot r n (-1), wrootE in PosRootFacts.v)     *)
(*   rootC_negroot C (RootC.v) : negroot (rootC_posroot C), w n = n.-root (-1) *)
(*   radcan_eq_cond_neg (Cond.v) : radcan_check_neg e1 e2 = Some cs ->       *)
(*                    all_conds r env cs -> rinterp r env e1 = rinterp r env e2 *)
(*   radcan_eq_refined_neg : the same with the refined conditions (Refine.v) *)
(*   radcan_eq_cond_rootC_neg, radcan_eq_refined_rootC_neg : on C, n.-root  *)
(* There is no negroot on a real field (-1 has no square root there); the   *)
(* real story is the oddroot of M6.                                          *)
(* The index law w (n * k) ^+ k = w n holds for the principal roots of C    *)
(* (arg omega_n = pi / n) but is not proved: the normaliser never merges     *)
(* omega atoms of different indices.                                         *)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts RootC Syntax Radcan Refine.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Lemma all_conds_gen_back (F : numFieldType) (r : posroot F) env cs :
  all_conds_gen (proot r) env cs -> all_conds r env cs.
Proof. by elim: cs => [|c cs IH] //=. Qed.

Theorem radcan_eq_refined_neg (F : numFieldType) (r : posroot F) (w : negroot r)
    (env : seq F) e1 e2 cs rcs :
  radcan_check_neg e1 e2 = Some cs -> refine cs = rcs ->
  all_rconds F (proot r) env rcs -> rinterp r env e1 = rinterp r env e2.
Proof.
move=> H Hr Hc; apply: (radcan_eq_cond_neg w H); apply: all_conds_gen_back.
by apply: refine_sound; rewrite Hr.
Qed.

(* on an algebraically closed field, with the principal roots n.-root *)
Theorem radcan_eq_cond_rootC_neg (C : numClosedFieldType) (env : seq C) e1 e2 cs :
  radcan_check_neg e1 e2 = Some cs -> all_conds (rootC_posroot C) env cs ->
  rinterp (rootC_posroot C) env e1 = rinterp (rootC_posroot C) env e2.
Proof. exact: (radcan_eq_cond_neg (rootC_negroot C)). Qed.

Theorem radcan_eq_refined_rootC_neg (C : numClosedFieldType) (env : seq C) e1 e2 cs rcs :
  radcan_check_neg e1 e2 = Some cs -> refine cs = rcs ->
  all_rconds C (proot (rootC_posroot C)) env rcs ->
  rinterp (rootC_posroot C) env e1 = rinterp (rootC_posroot C) env e2.
Proof. exact: (radcan_eq_refined_neg (rootC_negroot C)). Qed.

(* sanity checks on C *)
Section Checks.

Variable C : numClosedFieldType.

Lemma rootC_N1_sqr : 2.-root (-1 : C) ^+ 2 = -1.
Proof. exact: (prootN1K (rootC_negroot C)). Qed.

Lemma rootC_N4 : 2.-root (-4 : C) = 2 * 2.-root (-1).
Proof.
have -> : (-4 : C) = - (2 ^+ 2) by rewrite -natrX.
by rewrite rootC_prootNw // ?exprn_ge0 ?ler0n // -rootC_posrootE prootXK ?ler0n.
Qed.

End Checks.
