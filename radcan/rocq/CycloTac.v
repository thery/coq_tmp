(******************************************************************************)
(* CycloTac: the tactic of the cyclotomic checker (milestone Omega5).         *)
(*   radcan_cyc_with refined r w cy cp == reify, radcan_check_cyc, then       *)
(*                  radcan_eq_refined_cyc (refined) or radcan_eq_cond_cyc     *)
(*   radcan_cyc_only refined == the same, with cy : cycroot w and             *)
(*                  cp : cycprim w found in the context for a proot r goal,   *)
(*                  or the instances of C (CycC.v, CycloC.v) on n.-root goals *)
(*   radcan_cyc, radcan_cyc_raw == radcan first, then radcan_cyc_only         *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot RootC Syntax Radcan Refine OmegaRoot2.
From Radcan Require Import CycC Tactic Cyclo CycloC.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac radcan_cyc_with refined r w cy cp :=
  radcan_reify r;
  lazymatch goal with
  | |- rinterp _ ?env ?e1 = rinterp _ _ ?e2 =>
      let c := eval vm_compute in (radcan_check_cyc e1 e2) in
      lazymatch c with
      | Some ?cs =>
          lazymatch refined with
          | true =>
              let rcs := eval vm_compute in (refine cs) in
              apply: (@radcan_eq_refined_cyc _ r w cy cp env e1 e2 cs rcs);
                [radcan_vm_refl | radcan_vm_refl | radcan_split_rconds]
          | false =>
              apply: (@radcan_eq_cond_cyc _ r w cy cp env e1 e2 cs);
                [radcan_vm_refl | radcan_split_conds]
          end
      | None => fail "radcan_cyc: the normal forms differ"
      end
  end.

Ltac radcan_cyc_only refined :=
  lazymatch goal with
  | |- context [proot ?r _ _] =>
      lazymatch goal with
      | cy : @cycroot _ r ?w, cp : @cycprim _ r ?w |- _ =>
          radcan_cyc_with refined r w cy cp
      end
  | |- context [@nthroot ?C _ _] =>
      radcan_cyc_with refined (rootC_posroot C) (rootC_negroot C)
        (rootC_cycroot C) (rootC_cycprim C)
  end.

Ltac radcan_cyc_gen refined :=
  first [radcan_gen refined | radcan_cyc_only refined].

Ltac radcan_cyc := radcan_cyc_gen true.
Ltac radcan_cyc_raw := radcan_cyc_gen false.
