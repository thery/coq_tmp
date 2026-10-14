(* The normaliser on the Bignums backend (BigZ / BigQ) and its tactic.        *)
(*   RadcanBig := RadcanF BigNum   (RadcanBig.radcan_check,                  *)
(*                RadcanBig.radcan_eq_cond, RadcanBig.radcan_eq_cond0, ...)  *)
(*   radcan_big        == radcan using RadcanBig (same goals, same side       *)
(*                        conditions, faster on large numbers)                *)
(*   radcan_big_with r == the same with an explicit root structure r          *)
(* The names are qualified: importing this file does not change radcan.      *)

From Stdlib Require Import BinNums BinPos BinInt.
From Bignums Require Import BigZ BigQ.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot RootC RootR Syntax Radcan BigBackend Tactic.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Module RadcanBig := RadcanF BigNum.

Ltac radcan_big_with r :=
  radcan_reify r;
  lazymatch goal with
  | |- rinterp _ ?env ?e1 = rinterp _ _ ?e2 =>
      let c := eval vm_compute in (RadcanBig.radcan_check e1 e2) in
      lazymatch c with
      | Some ?cs =>
          apply: (@RadcanBig.radcan_eq_cond _ r env e1 e2 cs);
            [vm_compute; reflexivity | radcan_split_conds]
      | None => fail "radcan: the normal forms differ"
      end
  end.

Ltac radcan_big0 :=
  lazymatch goal with
  | |- @eq ?T ?a ?b =>
      let p := radcan_reify_term tt a (@nil T) in
      lazymatch p with (?ea, ?env1) =>
        let q := radcan_reify_term tt b env1 in
        lazymatch q with (?eb, ?env) =>
          change (rinterp0 env ea = rinterp0 env eb);
          let c := eval vm_compute in (RadcanBig.radcan_check ea eb) in
          lazymatch c with
          | Some ?cs =>
              apply: (@RadcanBig.radcan_eq_cond0 _ env ea eb cs erefl erefl);
                [vm_compute; reflexivity | radcan_split_conds]
          | None => fail "radcan: the normal forms differ"
          end
        end
      end
  end.

Ltac radcan_big :=
  lazymatch goal with
  | |- context [proot ?r _ _] => radcan_big_with r
  | |- context [@nthroot ?C _ _] => radcan_big_with (rootC_posroot C)
  | |- context [@rootR ?R _ _] => radcan_big_with (rootR_posroot R)
  | _ => radcan_big0
  end.

(* tests *)
Section Tests.
Variables (F : numFieldType) (r : posroot F) (x : F).

Lemma big_t1 : proot r 2 2 * proot r 2 3 = proot r 2 6. Proof. radcan_big. Qed.
Lemma big_t2 : 1 / (1 + proot r 2 2 + proot r 2 3) = (2 + proot r 2 2 - proot r 2 6) / 4.
Proof. radcan_big. Qed.
Lemma big_t3 : x - 1 != 0 -> (x ^+ 2 - 1) / (x - 1) = x + 1.
Proof. move=> h. radcan_big. exact: h. Qed.
Lemma big_t4 : 1 < x ->
  proot r 2 (x ^+ 2 - 1) / proot r 2 (x - 1) = proot r 2 (x + 1).
Proof.
move=> x_gt1. radcan_big.
- by rewrite addr_ge0 // ltW // (lt_trans ltr01 x_gt1).
- by rewrite subr_ge0 ltW.
- by rewrite subr_eq0 gt_eqF.
Qed.
End Tests.
