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
Local Notation "n .-proot" := (proot r n) (at level 2, format "n .-proot").
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).
Lemma d1 : 1 / \sqrt 2 = \sqrt 2 / 2. Proof. radcan. Qed.
Lemma d2 : 1 / (1 + \sqrt 2) = \sqrt 2 - 1. Proof. radcan. Qed.
Lemma d3 :
  (\sqrt 3 + \sqrt 2) / (\sqrt 3 - \sqrt 2) =
  5 + 2 * \sqrt 6.
Proof. radcan. Qed.
Lemma d4 : 1 / 3.-proot 2 = 3.-proot 4 / 2. Proof. radcan. Qed.
Lemma d5 :
  1 / (1 + \sqrt 2 + \sqrt 3) = (2 + \sqrt 2 - \sqrt 6) / 4.
Proof. radcan. Qed.
Lemma d6 : x / \sqrt 2 + x / \sqrt 2 = x * \sqrt 2.
Proof. radcan. Qed.
Lemma d7 : (x + \sqrt 2) / 3 = x / 3 + \sqrt 2 / 3.
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
