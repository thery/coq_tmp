(******************************************************************************)
(* Tutorial 11: the same base under several root indices.                     *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import Rstruct PosRoot RootC RootR Syntax Radcan Refine.
From Radcan Require Import Tactic RootRstd.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Section Generic.
Variables (F : numFieldType) (r : posroot F) (x y : F).
Local Notation "n .-proot" := (proot r n) (at level 2, format "n .-proot").
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).

(* sqrt x * cbrt x = 6th root of x^5 *)
Lemma i1 : 0 <= x -> \sqrt x * 3.-proot x = 6.-proot (x ^+ 5).
Proof. move=> x_ge0. radcan. Show. exact: x_ge0. Qed.

(* raw: 0 <= x, x != 0   refined: 0 < x *)
Lemma i2 : 0 < x -> \sqrt x / 3.-proot x = 6.-proot x.
Proof. move=> x_gt0. radcan. Show. exact: x_gt0. Qed.

Lemma i3 : 0 <= x -> 4.-proot x ^+ 2 = \sqrt x.
Proof. move=> x_ge0. radcan. exact: x_ge0. Qed.

Lemma i4 : 0 <= x -> 6.-proot (x ^+ 3) = \sqrt x.
Proof. move=> x_ge0. radcan. exact: x_ge0. Qed.

Lemma i5 : 1 <= x ->
  \sqrt (x - 1) * 3.-proot (x - 1) = 6.-proot ((x - 1) ^+ 5).
Proof. move=> x_ge1. radcan. Show. exact: x_ge1. Qed.

Lemma i6 : \sqrt 2 * 3.-proot x = 3.-proot x * \sqrt 2.
Proof. by radcan. Qed.

Lemma i7 : 0 <= x -> 0 <= y ->
  \sqrt (x * y) * 3.-proot x = 6.-proot (x ^+ 5) * \sqrt y.
Proof. move=> x_ge0 y_ge0. radcan. Show. all: by []. Qed.
End Generic.

Local Open Scope R_scope.
(* Stdlib has only sqrt: sqrt (sqrt x) is the root of the atom sqrt x *)
Lemma si1 (x : R) : 0 <= x -> sqrt x * sqrt (sqrt x) = sqrt (sqrt (x ^ 3)).
Proof.
move=> x_ge0. radcan_Rstd. radcan. Show.
(* 0 <= x (0 <= sqrt x follows from it and is dropped) *)
by radcan_Rstd_back; lra.
Qed.
