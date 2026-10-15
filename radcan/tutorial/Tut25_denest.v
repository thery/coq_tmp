(******************************************************************************)
(* Tutorial 25: denesting depth-two square roots (Denest.v, M19 phase 1).     *)
(*   denest_at r     == rewrites one proot r 2 t, t of the form a + b sqrt c, *)
(*                      into its candidate (denest_sound), then radcan        *)
(*   radcan_denest r == the whole goal through radcan_eq_denest              *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot RootR Syntax Radcan Tactic Denest.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* one nested root: reify its radicand t, find the candidate c, check
   denest_ok e c by vm_compute (the square by radcan_check, the sign by
   sq_nonneg), then rewrite with denest_sound: proot r 2 t = candidate *)
Ltac denest_at r :=
  match goal with
  | |- context [proot r 2 ?t] =>
    let T := type of t in
    let p := radcan_reify_term r t (@nil T) in
    lazymatch p with (?e, ?env) =>
      let c := eval vm_compute in (denest_find e) in
      lazymatch c with
      | Some ?c =>
        let H := fresh "H" in let h := fresh "h" in
        (have H : denest_ok e c by vm_compute);
        have h : proot r 2 t = rinterp r env (dc_rexpr c) :=
          denest_sound r env H;
        rewrite h {h H} /dc_rexpr /=
      end
    end
  end.

(* the whole goal at once: radcan_check on the denested sides *)
Ltac radcan_denest r :=
  radcan_reify r;
  lazymatch goal with
  | |- rinterp _ ?env ?e1 = rinterp _ _ ?e2 =>
    let c := eval vm_compute in (radcan_check_denest e1 e2) in
    lazymatch c with
    | Some ?cs =>
      apply: (@radcan_eq_denest _ r env e1 e2 cs);
        [vm_compute; reflexivity | radcan_split_conds]
    | None => fail "radcan_denest: the normal forms differ"
    end
  end.

Section Denest.
Variables (F : numFieldType) (r : posroot F).

(* plain radcan cannot do it: proot r 2 (3 + 2 sqrt 2) stays an atom *)
Goal proot r 2 (3 + 2 * proot r 2 2) = 1 + proot r 2 2.
Proof. Fail radcan. Abort.

Lemma d1 : proot r 2 (3 + 2 * proot r 2 2) = 1 + proot r 2 2.
Proof. denest_at r. radcan. Qed.

Lemma d2 : proot r 2 (5 + 2 * proot r 2 6) = proot r 2 2 + proot r 2 3.
Proof. denest_at r. radcan. Qed.

(* sign certificate: sqrt 3 - 1 >= 0 needs sqrt 3 >= 1 *)
Lemma d3 : proot r 2 (4 - 2 * proot r 2 3) = proot r 2 3 - 1.
Proof. denest_at r. radcan. Qed.

Lemma d4 : proot r 2 (7 - 4 * proot r 2 3) = 2 - proot r 2 3.
Proof. denest_at r. radcan. Qed.

(* rational coefficients: sqrt (3/2 + sqrt 2) = 1 + sqrt 2 / 2 *)
Lemma d5 : proot r 2 (3 / 2 + proot r 2 2) = 1 + proot r 2 2 / 2.
Proof. denest_at r. radcan. Qed.

(* the whole-goal version, several nested roots *)
Lemma d6 : proot r 2 (3 + 2 * proot r 2 2) - proot r 2 (3 - 2 * proot r 2 2)
  = 2.
Proof. radcan_denest r. Qed.

Lemma d7 : proot r 2 (12 + 6 * proot r 2 3) * proot r 2 (4 - 2 * proot r 2 3)
  = 2 * proot r 2 3.
Proof. radcan_denest r. Qed.

(* sqrt (1 + sqrt 2) does not denest: 1 - 2 = -1 is not a square *)
Goal proot r 2 (1 + proot r 2 2) = 0.
Proof. Fail denest_at r. Abort.

(* it stays as it is, and radcan_denest still proves what radcan proves *)
(* (the condition 0 <= sqrt 2 + 1 of the square of a root is left) *)
Lemma d8 : proot r 2 (1 + proot r 2 2) ^+ 2 = 1 + proot r 2 2.
Proof. radcan_denest r. by rewrite addr_ge0 ?proot_ge0. Qed.

(* a wrong candidate is refused: sqrt (4 - 2 sqrt 3) is not 1 - sqrt 3 *)
Goal proot r 2 (4 - 2 * proot r 2 3) = 1 - proot r 2 3.
Proof. Fail radcan_denest r. Abort.

End Denest.

(* on a real closed field, with rootR *)
Lemma rc_denest (R : rcfType) :
  rootR 2 (5 - 2 * rootR 2 6) = rootR 2 3 - rootR 2 (2 : R).
Proof. radcan_denest (rootR_posroot R). Qed.
