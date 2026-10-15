(******************************************************************************)
(* RealTactic: radcan on real fields (absolute values, odd roots of any       *)
(* sign), with the checker radcan_check_real (AbsRoot.v).                     *)
(*   radcan_real     == like radcan: |a| is first rewritten into              *)
(*                      proot r 2 (a ^+ 2) (normr_proot, normr_rootR), then   *)
(*                      both sides are normalised in mode MRealA (|B| for     *)
(*                      even roots of even powers, no condition), else MReal  *)
(*                      (B with 0 <= B); odd roots need no sign condition     *)
(*   radcan_real_raw == the same with the raw conditions                      *)
(* Root structures: rootR (rootR_realroot), or proot r with rl : realroot r   *)
(* in the context.                                                            *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot RootC RootR RealRoot Syntax Radcan Refine.
From Radcan Require Import AbsRoot Tactic.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Ltac radcan_real_with_gen refined r rl :=
  radcan_reify r;
  lazymatch goal with
  | |- rinterp _ ?env ?e1 = rinterp _ _ ?e2 =>
      let c := eval vm_compute in (radcan_check_real e1 e2) in
      lazymatch c with
      | Some ?cs =>
          lazymatch refined with
          | true =>
              let rcs := eval vm_compute in (refine cs) in
              apply: (@radcan_eq_refined_real _ r rl env e1 e2 cs rcs);
                [vm_compute; reflexivity | vm_compute; reflexivity
                | radcan_split_rconds]
          | false =>
              apply: (@radcan_eq_cond_real _ r rl env e1 e2 cs);
                [vm_compute; reflexivity | radcan_split_conds]
          end
      | None => fail "radcan: the normal forms differ"
      end
  end.

Ltac radcan_real_gen refined :=
  rewrite ?normr_rootR;
  lazymatch goal with
  | |- context [@rootR ?R _ _] =>
      radcan_real_with_gen refined (rootR_posroot R) (rootR_realroot R)
  | rl : realroot ?r |- _ =>
      rewrite ?(normr_proot rl); radcan_real_with_gen refined r rl
  | _ => fail "radcan_real: no rootR and no realroot in the context"
  end.

Ltac radcan_real := radcan_real_gen true.
Ltac radcan_real_raw := radcan_real_gen false.
