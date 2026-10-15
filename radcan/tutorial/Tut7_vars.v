(******************************************************************************)
(* Tutorial 7: radcan with variables and atoms.                               *)
(******************************************************************************)

From Stdlib Require Import Reals.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import Rstruct PosRoot RootC RootR Syntax Radcan Tactic.
From Radcan Require Import RootRstd.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Section Generic.
Variables (F : numFieldType) (r : posroot F) (x y : F).
Local Notation "n .-proot" := (proot r n) (at level 2, format "n .-proot").
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).
Lemma v1 : x * \sqrt 2 = \sqrt 2 * x. Proof. radcan. Qed.
Lemma v2 : x * \sqrt 2 + x * \sqrt 2 = 2 * x * \sqrt 2.
Proof. radcan. Qed.
Lemma v3 : (x + \sqrt 2) ^+ 2 = x ^+ 2 + 2 * x * \sqrt 2 + 2.
Proof. radcan. Qed.
Lemma v4 : (x - y * \sqrt 3) * (x + y * \sqrt 3) = x ^+ 2 - 3 * y ^+ 2.
Proof. radcan. Qed.
Lemma v5 : (x + 3.-proot 2) ^+ 3
         = x ^+ 3 + 3 * x ^+ 2 * 3.-proot 2 + 3 * x * 3.-proot 4 + 2.
Proof. radcan. Qed.
(* any unrecognised subterm is an atom, e.g. sin x on R or f x here *)
Variable f : F -> F.
Lemma v6 : f x * \sqrt 8 = 2 * \sqrt 2 * f x.
Proof. radcan. Qed.
End Generic.

Local Open Scope R_scope.
Lemma s4 (x y : R) : (x - y * sqrt 3) * (x + y * sqrt 3) = x ^ 2 - 3 * y ^ 2.
Proof. radcan_Rstd. radcan. Qed.
Lemma s5 (x : R) : (x + sqrt 2) ^ 2 = x ^ 2 + 2 * sqrt 2 * x + 2.
Proof. radcan_Rstd. radcan. Qed.
Lemma s6 (x : R) : sin x * sqrt 8 = 2 * sqrt 2 * sin x.
Proof. radcan_Rstd. radcan. Qed.
