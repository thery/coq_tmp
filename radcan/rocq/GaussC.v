(******************************************************************************)
(* GaussC: the Gauss-sum facts of the principal roots of -1 on C.             *)
(*   rootC_gaussroot C : gaussroot (rootC_negroot C)   (GaussMode.v), from    *)
(*                       omega4_sqrt2C (OmegaC.v), sqrtC_gauss_1mod4 and      *)
(*                       sqrtC_gauss_3mod4 (GaussSum.v)                       *)
(*   radcan_eq_cond_rootC_gauss, radcan_eq_refined_rootC_gauss == the         *)
(*                       decision theorems of radcan_check_gauss on n.-root   *)
(*                       goals                                                *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot RootC Syntax Radcan Refine OmegaRoot2.
From Radcan Require Import OmegaC GaussSum CycC Cyclo CycloC GaussMode.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section GaussC.

Variable C : numClosedFieldType.

(* wroot (rootC_negroot C) n is n.-root (-1), proot .. 2 is sqrtC *)
Lemma rootC_gaussroot : gaussroot (rootC_negroot C).
Proof.
split=> /=; first by rewrite omega4_sqrt2C.
  by move=> n n4; exact: sqrtC_gauss_1mod4.
by move=> n n4; exact: sqrtC_gauss_3mod4.
Qed.

Theorem radcan_eq_cond_rootC_gauss (env : seq C) e1 e2 cs :
  radcan_check_gauss e1 e2 = Some cs -> all_conds (rootC_posroot C) env cs ->
  rinterp (rootC_posroot C) env e1 = rinterp (rootC_posroot C) env e2.
Proof.
exact: (radcan_eq_cond_gauss (rootC_cycroot C) (rootC_cycprim C)
          rootC_gaussroot).
Qed.

Theorem radcan_eq_refined_rootC_gauss (env : seq C) e1 e2 cs rcs :
  radcan_check_gauss e1 e2 = Some cs -> refine cs = rcs ->
  all_rconds C (proot (rootC_posroot C)) env rcs ->
  rinterp (rootC_posroot C) env e1 = rinterp (rootC_posroot C) env e2.
Proof.
exact: (radcan_eq_refined_gauss (rootC_cycroot C) (rootC_cycprim C)
          rootC_gaussroot).
Qed.

End GaussC.
