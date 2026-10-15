(******************************************************************************)
(* Tutorial 28 (Omega2): explicit values of the small roots of unity.         *)
(* In neg mode (Tutorial 16) omega_n = n.-root (-1) is an atom reduced only   *)
(* by omega_n ^+ n = -1.  For 2 n | 24 it has a value in square roots and     *)
(* omega_2 (= 'i on C):                                                       *)
(*   omega_3 = (1 + sqrt 3 omega_2) / 2     omega_4 = sqrt 2 / 2 (1 + omega_2)*)
(*   omega_6 = (sqrt 3 + omega_2) / 2                                         *)
(*   omega_12 = (sqrt 6 + sqrt 2 + (sqrt 6 - sqrt 2) omega_2) / 4             *)
(* collected in the record smallroot w (OmegaRoot.v).  omega_rw (OmegaPass.v) *)
(* rewrites every n.-root a, n = 3, 4, 6, 12, with a radicand                 *)
(*   - a negative constant - p / d : into n.-root (p / d) * omega_n,          *)
(*   - with a negative last monomial (e.g. 1 - x): into                       *)
(*     n.-root (- a) * omega_n under the condition 0 <= - a,                  *)
(* and every n.-root (P / Q) with a variable (any n): the signs of P and Q    *)
(* are tested apart (Tutorial 31),                                            *)
(* and radcan_eq_omega* run radcan_check_neg on the result.                   *)
(*   radcan_omega == radcan, and on failure omega_rw + radcan_check_neg       *)
(*                   (local Ltac; radcan itself now runs omega_rw in its      *)
(*                   composed pre-pass, Tutorial 29)                          *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts RootC Syntax.
From Radcan Require Import Radcan Refine Tactic NegRootC OmegaRoot OmegaC.
From Radcan Require Import OmegaPass.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* radcan_with_gen of Tactic.v in neg mode, with omega_rw before the checker *)
Ltac radcan_omega_with_gen refined r w ov :=
  radcan_reify r;
  lazymatch goal with
  | |- rinterp _ ?env ?e1 = rinterp _ _ ?e2 =>
      let p1 := eval vm_compute in (omega_rw e1) in
      let p2 := eval vm_compute in (omega_rw e2) in
      lazymatch p1 with (?f1, ?cs1) =>
      lazymatch p2 with (?f2, ?cs2) =>
      let c := eval vm_compute in (radcan_check_neg f1 f2) in
      lazymatch c with
      | Some ?cs =>
          lazymatch refined with
          | true =>
              let rcs := eval vm_compute in (refine (cs1 ++ cs2 ++ cs)) in
              apply: (@radcan_eq_omega_refined _ r w env ov
                        e1 e2 f1 f2 cs1 cs2 cs rcs);
              [vm_compute; reflexivity | vm_compute; reflexivity
              | vm_compute; reflexivity | vm_compute; reflexivity
              | radcan_split_rconds]
          | false =>
              apply: (@radcan_eq_omega _ r w env ov
                        e1 e2 f1 f2 cs1 cs2 cs);
              [vm_compute; reflexivity | vm_compute; reflexivity
              | vm_compute; reflexivity | radcan_split_conds]
          end
      | None => fail "radcan_omega: the normal forms differ"
      end end end
  end.

(* the dispatch: a proot r goal with ov : smallroot w (w : negroot r), or  *)
(* an n.-root goal on C (rootC_negroot C, rootC_smallroot C of OmegaC.v)    *)
Ltac radcan_omega_only refined :=
  lazymatch goal with
  | |- context [proot ?r _ _] =>
      lazymatch goal with
      | ov : @smallroot _ r ?w |- _ => radcan_omega_with_gen refined r w ov
      end
  | |- context [@nthroot ?C _ _] =>
      radcan_omega_with_gen refined (rootC_posroot C) (rootC_negroot C)
        (rootC_smallroot C)
  end.

(* plain radcan first, so that the goals it proves keep their conditions *)
Ltac radcan_omega_gen refined :=
  first [radcan_gen refined | radcan_omega_only refined].

Ltac radcan_omega := radcan_omega_gen true.
Ltac radcan_omega_raw := radcan_omega_gen false.

Section Generic.
Variables (F : numFieldType) (r : posroot F) (w : negroot r).
Hypothesis ov : smallroot w.
Variable x : F.
Local Notation "\w_ n" := (proot r n (-1)) (at level 3, n at level 2).

Lemma o1 : \w_3 ^+ 2 - \w_3 + 1 = 0.
Proof. Fail radcan_plain_gen true. Time radcan_omega. Qed.

(* the index law, through the explicit values *)
Lemma o2 : \w_4 ^+ 2 = \w_2.
Proof. Fail radcan_plain_gen true. Time radcan_omega. Qed.

Lemma o3 : \w_6 ^+ 2 = \w_3.
Proof. Fail radcan_plain_gen true. Time radcan_omega. Qed.

Lemma o4 : \w_12 ^+ 3 = \w_4.
Proof. Fail radcan_plain_gen true. Time radcan_omega. Qed.

Lemma o5 : \w_6 ^+ 3 = \w_2.
Proof. Fail radcan_plain_gen true. Time radcan_omega. Qed.

Lemma o6 : \w_12 ^+ 2 = \w_6.
Proof. Time radcan_omega. Qed.

(* omega_4 + omega_4 ^-1 = sqrt 2 *)
Lemma o7 : \w_4 + (\w_4)^-1 = proot r 2 2.
Proof. Fail radcan_plain_gen true. Time radcan_omega. Qed.

(* negative constant radicands: n.-root (- p / d) = n.-root (p / d) omega_n *)
Lemma o8 : proot r 3 (-8) = 1 + proot r 2 3 * \w_2.
Proof. Fail radcan_plain_gen true. Time radcan_omega. Qed.

Lemma o9 : proot r 4 (- (1 / 4)) = (1 + \w_2) / 2.
Proof. Fail radcan_plain_gen true. Time radcan_omega. Qed.

Lemma o10 : proot r 12 (-1) ^+ 4 = proot r 3 (-1).
Proof. Time radcan_omega. Qed.

(* the paper's (2), second reading ((1 - x)^(3/4) = ((1 - x)^(1/4))^3):     *)
(* 4.-root (1 - x) = 4.-root (x - 1) * omega_4 under 0 <= x - 1, so the     *)
(* left side is omega_4^-1 - omega_4^-3 - sqrt 2 = 0                        *)
(* raw: 0 <= - (1 - x) (omega_rw, twice), 0 <= x - 1, x - 1 != 0           *)
(* refined: 1 < x                                                           *)
Lemma paper2 : 1 < x ->
  proot r 4 (x - 1) / proot r 4 (1 - x)
  - proot r 4 (x - 1) ^+ 3 / proot r 4 (1 - x) ^+ 3 - proot r 2 2 = 0.
Proof. move=> h. Fail radcan_plain_gen true. Time radcan_omega. exact: h. Qed.

(* first reading ((1 - x)^(3/4) = 4.-root ((1 - x)^3)): the principal roots *)
(* make the first two terms cancel, so the left side of (2) is - sqrt 2;   *)
(* plain radcan already proves it (the omega_4 atoms cancel)               *)
Lemma paper2' : 1 < x ->
  proot r 4 (x - 1) / proot r 4 (1 - x)
  - proot r 4 ((x - 1) ^+ 3) / proot r 4 ((1 - x) ^+ 3) = 0.
Proof. move=> h. radcan. exact: h. Qed.
End Generic.

(* On C: n.-root goals, with rootC_negroot C and rootC_smallroot C (OmegaC.v) *)
Section Complex.
Variables (C : numClosedFieldType) (x : C).

(* the two Fail goals of TUTORIAL Part 16 *)
Lemma c1 : 3.-root (-1 : C) ^+ 2 - 3.-root (-1) + 1 = 0.
Proof. Fail radcan_plain_gen true. Time radcan_omega. Qed.

Lemma c2 : 4.-root (-1 : C) ^+ 2 = 2.-root (-1).
Proof. Fail radcan_plain_gen true. Time radcan_omega. Qed.

Lemma c3 : 6.-root (-1 : C) ^+ 2 = 3.-root (-1).
Proof. Fail radcan_plain_gen true. Time radcan_omega. Qed.

Lemma c4 : 12.-root (-1 : C) ^+ 3 = 4.-root (-1).
Proof. Fail radcan_plain_gen true. Time radcan_omega. Qed.

(* the principal cube root of -8 *)
Lemma c5 : 3.-root (-8 : C) = 1 + 2.-root 3 * 2.-root (-1).
Proof. Fail radcan_plain_gen true. Time radcan_omega. Qed.

(* paper (2), second reading; refined: 1 < x *)
Lemma c6 : 1 < x ->
  4.-root (x - 1) / 4.-root (1 - x)
  - 4.-root (x - 1) ^+ 3 / 4.-root (1 - x) ^+ 3 - 2.-root 2 = 0.
Proof. move=> h. Fail radcan_plain_gen true. Time radcan_omega. exact: h. Qed.
End Complex.
