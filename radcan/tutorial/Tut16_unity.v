(******************************************************************************)
(* Tutorial 16: roots of negatives on C through omega_n = n.-root (-1),       *)
(* omega_n ^+ n = -1, n.-root (- a) = n.-root a * omega_n for 0 <= a.         *)
(* radcan uses it on n.-root goals, and on proot r goals with a negroot r     *)
(* in the context (theorem radcan_eq_refined_neg, NegRootC.v).                *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts RootC Syntax Radcan Refine.
From Radcan Require Import Tactic NegRootC.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Section Unity.
Variables (C : numClosedFieldType) (x : C).

(* sqrt (-4) = 2 omega_2 *)
Lemma u1 : 2.-root (-4 : C) = 2 * 2.-root (-1).
Proof. by radcan. Qed.

Lemma u2 : 2.-root (-1 : C) ^+ 2 = -1.
Proof. by radcan. Qed.

(* true for the principal roots: i sqrt 2 * i sqrt 8 = -4 *)
Lemma u3 : 2.-root (-2 : C) * 2.-root (-8) = -4.
Proof. by radcan. Qed.

Lemma u4 : 3.-root (-8 : C) ^+ 3 = -8.
Proof. by radcan. Qed.

(* the principal cube root of -8 is 2 omega_3, not -2 *)
Lemma u5 : 3.-root (-8 : C) = 2 * 3.-root (-1).
Proof. by radcan. Qed.

Goal 3.-root (-8 : C) = -2.
Proof. Fail radcan. Abort.

Lemma u6 :
  2.-root (-3 : C) * 2.-root (-3) * 2.-root (-3) = -3 * 2.-root (-3).
Proof. by radcan. Qed.

Lemma u7 : (1 + 2.-root (-1 : C)) ^+ 2 = 2 * 2.-root (-1).
Proof. by radcan. Qed.

(* omega_n ^-1 = - omega_n ^+ (n - 1) *)
Lemma u8 : 1 / 2.-root (-1 : C) = - 2.-root (-1).
Proof. by radcan. Qed.

Lemma u9 : 1 / 3.-root (-2 : C) = - 3.-root (-1) ^+ 2 * 3.-root 4 / 2.
Proof. by radcan. Qed.

(* omega_3 is a root of x^2 - x + 1: not found, omega atoms are only
   reduced by omega_n ^+ n = -1 (no cyclotomic relation) *)
Goal 3.-root (-1 : C) ^+ 2 - 3.-root (-1) + 1 = 0.
Proof. Fail radcan. Abort.

(* omega atoms of different indices are not merged (no index law) *)
Goal 4.-root (-1 : C) ^+ 2 = 2.-root (-1).
Proof. Fail radcan. Abort.

(* a polynomial radicand with no base to flip;
   raw: 0 <= x - 1, refined: 1 <= x *)
Lemma u10 : 1 <= x -> 2.-root (- (x - 1) ^+ 2) = (x - 1) * 2.-root (-1).
Proof. move=> x_ge1. radcan. Show. exact: x_ge1. Qed.

End Unity.

(* with any posroot r and a negroot w in the context *)
Section Generic.
Variables (F : numFieldType) (r : posroot F) (w : negroot r).

Lemma g1 : proot r 2 (- 2) * proot r 2 (- 8) = - 4.
Proof. by radcan. Qed.

End Generic.
