(******************************************************************************)
(* NegCyc: decision theorem of the neg mode merging omega atoms across        *)
(* indices (modes MNegC, MNegCW of CondSimp.v), for a posroot r with a        *)
(* negroot w satisfying the index law cycroot w (OmegaRoot2.v).               *)
(*   radcan_eq_refined_negc cy : radcan_check_negc e1 e2 = Some cs ->         *)
(*      refine cs = rcs -> all_rconds .. rcs -> rinterp r env e1 = .. e2      *)
(* (radcan_eq_cond_negc is in Cond.v; the instances on C in CycC.v.)         *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot Syntax Radcan Refine OmegaRoot2.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Theorem radcan_eq_refined_negc (F : numFieldType) (r : posroot F)
    (w : negroot r) (cy : cycroot w) (env : seq F) e1 e2 cs rcs :
  radcan_check_negc e1 e2 = Some cs -> refine cs = rcs ->
  all_rconds F (proot r) env rcs -> rinterp r env e1 = rinterp r env e2.
Proof.
move=> H Hr Hc; apply: (radcan_eq_cond_negc cy H); apply: all_conds_bridge_back.
by apply: refine_sound; rewrite Hr.
Qed.
