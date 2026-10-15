(******************************************************************************)
(* NegRootC: decision theorems of the neg mode (roots of negatives through    *)
(* roots of -1), for a posroot r with a negroot w.                            *)
(*   radcan_eq_refined_neg w : radcan_check_neg e1 e2 = Some cs ->            *)
(*      refine cs = rcs -> all_rconds .. rcs -> rinterp r env e1 = .. e2      *)
(*   radcan_eq_cond_rootC_neg, radcan_eq_refined_rootC_neg : the instances    *)
(*      on a numClosedFieldType with n.-root                                  *)
(* (radcan_eq_cond_neg is in Cond.v.)  Plain neg mode does not merge omega   *)
(* atoms of different indices; the modes of NegCyc.v (index law, record      *)
(* cycroot) and Cyclo.v (cyclotomic reduction) do.                            *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts RootC Syntax Radcan Refine.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Theorem radcan_eq_refined_neg (F : numFieldType) (r : posroot F)
    (w : negroot r) (env : seq F) e1 e2 cs rcs :
  radcan_check_neg e1 e2 = Some cs -> refine cs = rcs ->
  all_rconds F (proot r) env rcs -> rinterp r env e1 = rinterp r env e2.
Proof.
move=> H Hr Hc; apply: (radcan_eq_cond_neg w H); apply: all_conds_bridge_back.
by apply: refine_sound; rewrite Hr.
Qed.

Theorem radcan_eq_cond_rootC_neg (C : numClosedFieldType) (env : seq C)
    e1 e2 cs :
  radcan_check_neg e1 e2 = Some cs -> all_conds (rootC_posroot C) env cs ->
  rinterp (rootC_posroot C) env e1 = rinterp (rootC_posroot C) env e2.
Proof. exact: (radcan_eq_cond_neg (rootC_negroot C)). Qed.

Theorem radcan_eq_refined_rootC_neg (C : numClosedFieldType) (env : seq C)
    e1 e2 cs rcs :
  radcan_check_neg e1 e2 = Some cs -> refine cs = rcs ->
  all_rconds C (proot (rootC_posroot C)) env rcs ->
  rinterp (rootC_posroot C) env e1 = rinterp (rootC_posroot C) env e2.
Proof. exact: (radcan_eq_refined_neg (rootC_negroot C)). Qed.

(* Sanity checks on C. *)
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
