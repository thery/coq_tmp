(******************************************************************************)
(* AbsRoot: decision theorems of the real mode (absolute values, odd roots    *)
(* of any sign), for a posroot r with a realroot rl (RealRoot.v).             *)
(*   radcan_eq_refined_real rl : radcan_check_real e1 e2 = Some cs ->         *)
(*      refine cs = rcs -> all_rconds .. rcs -> rinterp r env e1 = .. e2      *)
(*   radcan_eq_cond_rootR_real, radcan_eq_refined_rootR_real : the instances  *)
(*      on an rcfType with rootR                                              *)
(* (radcan_eq_cond_real itself is in Cond.v.)  |B| enters a goal as           *)
(* proot r 2 (B ^+ 2) (normr_proot, normr_rootR).                             *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts RootR RealRoot Syntax Radcan.
From Radcan Require Import Refine.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Theorem radcan_eq_refined_real (F : numFieldType) (r : posroot F)
    (rl : realroot r) (env : seq F) e1 e2 cs rcs :
  radcan_check_real e1 e2 = Some cs -> refine cs = rcs ->
  all_rconds F (proot r) env rcs -> rinterp r env e1 = rinterp r env e2.
Proof.
move=> H Hr Hc; apply: (radcan_eq_cond_real rl H); apply: all_conds_bridge_back.
by apply: refine_sound; rewrite Hr.
Qed.

Theorem radcan_eq_cond_rootR_real (R : rcfType) (env : seq R) e1 e2 cs :
  radcan_check_real e1 e2 = Some cs -> all_conds (rootR_posroot R) env cs ->
  rinterp (rootR_posroot R) env e1 = rinterp (rootR_posroot R) env e2.
Proof. exact: (radcan_eq_cond_real (rootR_realroot R)). Qed.

Theorem radcan_eq_refined_rootR_real (R : rcfType) (env : seq R) e1 e2 cs rcs :
  radcan_check_real e1 e2 = Some cs -> refine cs = rcs ->
  all_rconds R (proot (rootR_posroot R)) env rcs ->
  rinterp (rootR_posroot R) env e1 = rinterp (rootR_posroot R) env e2.
Proof. exact: (radcan_eq_refined_real (rootR_realroot R)). Qed.
