(******************************************************************************)
(* CycC: the index law of the principal roots of -1 on C (milestone Omega4).  *)
(* rootC_N1_index is the index law of UnitArc.v (Omega3).                     *)
(*   rootC_cycroot C : cycroot (rootC_negroot C)   (OmegaRoot2.v)             *)
(*   radcan_eq_cond_rootC_negc, radcan_eq_refined_rootC_negc : the decision  *)
(*      theorems of radcan_check_negc on n.-root goals                        *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot RootC Syntax Radcan Refine OmegaRoot2.
From Radcan Require Import NegCyc UnitArc.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section CycC.

Variable C : numClosedFieldType.

(* wroot (rootC_negroot C) n is n.-root (-1) by conversion *)
Lemma rootC_cycroot : cycroot (rootC_negroot C).
Proof. by split=> n k n0 k0; exact: rootC_N1_index. Qed.

Theorem radcan_eq_cond_rootC_negc (env : seq C) e1 e2 cs :
  radcan_check_negc e1 e2 = Some cs -> all_conds (rootC_posroot C) env cs ->
  rinterp (rootC_posroot C) env e1 = rinterp (rootC_posroot C) env e2.
Proof. exact: (radcan_eq_cond_negc rootC_cycroot). Qed.

Theorem radcan_eq_refined_rootC_negc (env : seq C) e1 e2 cs rcs :
  radcan_check_negc e1 e2 = Some cs -> refine cs = rcs ->
  all_rconds C (proot (rootC_posroot C)) env rcs ->
  rinterp (rootC_posroot C) env e1 = rinterp (rootC_posroot C) env e2.
Proof. exact: (radcan_eq_refined_negc rootC_cycroot). Qed.

End CycC.
