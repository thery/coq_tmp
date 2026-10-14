(******************************************************************************)
(* Tutorial 8: radcan with division.                                          *)
(******************************************************************************)

From Stdlib Require Import Reals.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import Rstruct PosRoot RootC RootR Syntax Radcan Tactic.
From Radcan Require Import RootRstd.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Section Generic.
Variables (F : numFieldType) (r : posroot F) (x : F).
Lemma d1 : 1 / proot r 2 2 = proot r 2 2 / 2. Proof. radcan. Qed.
Lemma d2 : 1 / (1 + proot r 2 2) = proot r 2 2 - 1. Proof. radcan. Qed.
Lemma d3 :
  (proot r 2 3 + proot r 2 2) / (proot r 2 3 - proot r 2 2) =
  5 + 2 * proot r 2 6.
Proof. radcan. Qed.
Lemma d4 : 1 / proot r 3 2 = proot r 3 4 / 2. Proof. radcan. Qed.
Lemma d5 :
  1 / (1 + proot r 2 2 + proot r 2 3) = (2 + proot r 2 2 - proot r 2 6) / 4.
Proof. radcan. Qed.
Lemma d6 : x / proot r 2 2 + x / proot r 2 2 = x * proot r 2 2.
Proof. radcan. Qed.
Lemma d7 : (x + proot r 2 2) / 3 = x / 3 + proot r 2 2 / 3.
Proof. radcan. Qed.
End Generic.

Lemma dc (C : numClosedFieldType) : 1 / (1 + 2.-root 2) = 2.-root 2 - 1 :> C.
Proof. radcan. Qed.

Local Open Scope R_scope.
Lemma sd1 : 1 / sqrt 2 = sqrt 2 / 2. Proof. radcan_Rstd. radcan. Qed.
Lemma sd2 : / (sqrt 3 - sqrt 2) = sqrt 3 + sqrt 2.
Proof. radcan_Rstd. radcan. Qed.

(* a false goal is refused *)
Goal 1 / sqrt 2 = sqrt 2. Proof. radcan_Rstd. Fail radcan. Abort.

Print Assumptions d5.
Print Assumptions sd2.
