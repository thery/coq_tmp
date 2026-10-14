(******************************************************************************)
(* OddRoot: decision theorems of the odd mode (negative radicands under odd   *)
(* roots), for a posroot r with an oddroot o.                                 *)
(*   radcan_eq_refined_odd o : radcan_check_odd e1 e2 = Some cs ->            *)
(*      refine cs = rcs -> all_rconds .. rcs -> rinterp r env e1 = .. e2      *)
(*   radcan_eq_cond_rootR, radcan_eq_refined_rootR : the instances on an      *)
(*      rcfType with rootR (radcan_eq_cond_odd itself is in Cond.v)           *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts RootR Syntax Radcan Refine.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Theorem radcan_eq_refined_odd (F : numFieldType) (r : posroot F)
    (o : oddroot r) (env : seq F) e1 e2 cs rcs :
  radcan_check_odd e1 e2 = Some cs -> refine cs = rcs ->
  all_rconds F (proot r) env rcs -> rinterp r env e1 = rinterp r env e2.
Proof.
move=> H Hr Hc; apply: (radcan_eq_cond_odd o H); apply: all_conds_bridge_back.
by apply: refine_sound; rewrite Hr.
Qed.

Theorem radcan_eq_cond_rootR (R : rcfType) (env : seq R) e1 e2 cs :
  radcan_check_odd e1 e2 = Some cs -> all_conds (rootR_posroot R) env cs ->
  rinterp (rootR_posroot R) env e1 = rinterp (rootR_posroot R) env e2.
Proof. exact: (radcan_eq_cond_odd (rootR_oddroot R)). Qed.

Theorem radcan_eq_refined_rootR (R : rcfType) (env : seq R) e1 e2 cs rcs :
  radcan_check_odd e1 e2 = Some cs -> refine cs = rcs ->
  all_rconds R (proot (rootR_posroot R)) env rcs ->
  rinterp (rootR_posroot R) env e1 = rinterp (rootR_posroot R) env e2.
Proof. exact: (radcan_eq_refined_odd (rootR_oddroot R)). Qed.
