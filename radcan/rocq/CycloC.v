(******************************************************************************)
(* CycloC: the principal roots of -1 on C are primitive (milestone Omega5).   *)
(*   rootC_cycprim C : cycprim (rootC_negroot C)   (Cyclo.v), from            *)
(*                     rootC_N1_prim of UnitArc.v                             *)
(*   radcan_eq_cond_rootC_cyc, radcan_eq_refined_rootC_cyc == the decision    *)
(*                     theorems of radcan_check_cyc on n.-root goals          *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot RootC Syntax Radcan Refine OmegaRoot2.
From Radcan Require Import UnitArc CycC Cyclo.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section CycloC.

Variable C : numClosedFieldType.

(* wroot (rootC_negroot C) n is n.-root (-1) by conversion *)
Lemma rootC_cycprim : cycprim (rootC_negroot C).
Proof. by split=> n n0; exact: rootC_N1_prim. Qed.

Theorem radcan_eq_cond_rootC_cyc (env : seq C) e1 e2 cs :
  radcan_check_cyc e1 e2 = Some cs -> all_conds (rootC_posroot C) env cs ->
  rinterp (rootC_posroot C) env e1 = rinterp (rootC_posroot C) env e2.
Proof. exact: (radcan_eq_cond_cyc (rootC_cycroot C) rootC_cycprim). Qed.

Theorem radcan_eq_refined_rootC_cyc (env : seq C) e1 e2 cs rcs :
  radcan_check_cyc e1 e2 = Some cs -> refine cs = rcs ->
  all_rconds C (proot (rootC_posroot C)) env rcs ->
  rinterp (rootC_posroot C) env e1 = rinterp (rootC_posroot C) env e2.
Proof. exact: (radcan_eq_refined_cyc (rootC_cycroot C) rootC_cycprim). Qed.

End CycloC.
