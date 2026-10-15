(******************************************************************************)
(* Tutorial 6: the radcan tactic on constant radicals.                        *)
(******************************************************************************)

From Stdlib Require Import Reals.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import Rstruct PosRoot RootC RootR Syntax Radcan Tactic.
From Radcan Require Import RootRstd.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Section Generic.
Variables (F : numFieldType) (r : posroot F).
Local Notation "n .-proot" := (proot r n) (at level 2, format "n .-proot").
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).
Lemma g1 : \sqrt 2 * \sqrt 3 = \sqrt 6. Proof. radcan. Qed.
Lemma g2 : (1 + \sqrt 2) ^+ 2 = 3 + 2 * \sqrt 2. Proof. radcan. Qed.
Lemma g3 : \sqrt 8 = 2 * \sqrt 2. Proof. radcan. Qed.
Lemma g4 : 3.-proot 2 * \sqrt 2 = 6.-proot 32. Proof. radcan. Qed.
Lemma g5 : \sqrt 12 - \sqrt 3 = \sqrt 3. Proof. radcan. Qed.
End Generic.

Lemma c1 (C : numClosedFieldType) : (3.-root 2) * (2.-root 2) = 6.-root 32 :> C.
Proof. radcan. Qed.

Lemma rc1 (R : rcfType) :
  (rootR 2 2 + rootR 2 3) ^+ 2 = 5 + 2 * rootR 2 (6 : R).
Proof. radcan. Qed.

Local Open Scope R_scope.
Lemma s1 : sqrt 2 * sqrt 3 = sqrt 6. Proof. radcan_Rstd. radcan. Qed.
Lemma s2 : (1 + sqrt 2) ^ 2 = 3 + 2 * sqrt 2. Proof. radcan_Rstd. radcan. Qed.
Lemma s3 : sqrt 12 - sqrt 3 = sqrt 3. Proof. radcan_Rstd. radcan. Qed.

Goal sqrt 2 + sqrt 3 = sqrt 5.
Proof. radcan_Rstd. Fail radcan. Abort.
