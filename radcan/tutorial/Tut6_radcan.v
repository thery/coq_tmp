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
Lemma g1 : proot r 2 2 * proot r 2 3 = proot r 2 6. Proof. radcan. Qed.
Lemma g2 : (1 + proot r 2 2) ^+ 2 = 3 + 2 * proot r 2 2. Proof. radcan. Qed.
Lemma g3 : proot r 2 8 = 2 * proot r 2 2. Proof. radcan. Qed.
Lemma g4 : proot r 3 2 * proot r 2 2 = proot r 6 32. Proof. radcan. Qed.
Lemma g5 : proot r 2 12 - proot r 2 3 = proot r 2 3. Proof. radcan. Qed.
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
