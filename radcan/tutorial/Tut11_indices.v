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

(* sqrt x * cbrt x = 6th root of x^5 *)
Lemma i1 : 0 <= x -> proot r 2 x * proot r 3 x = proot r 6 (x ^+ 5).
Proof. move=> x_ge0. radcan. Show. exact: x_ge0. Qed.

(* raw: 0 <= x, x != 0   refined: 0 < x *)
Lemma i2 : 0 < x -> proot r 2 x / proot r 3 x = proot r 6 x.
Proof. move=> x_gt0. radcan. Show. exact: x_gt0. Qed.

Lemma i3 : 0 <= x -> proot r 4 x ^+ 2 = proot r 2 x.
Proof. move=> x_ge0. radcan. exact: x_ge0. Qed.

Lemma i4 : 0 <= x -> proot r 6 (x ^+ 3) = proot r 2 x.
Proof. move=> x_ge0. radcan. exact: x_ge0. Qed.

Lemma i5 : 1 <= x ->
  proot r 2 (x - 1) * proot r 3 (x - 1) = proot r 6 ((x - 1) ^+ 5).
Proof. move=> x_ge1. radcan. Show. exact: x_ge1. Qed.

Lemma i6 : proot r 2 2 * proot r 3 x = proot r 3 x * proot r 2 2.
Proof. by radcan. Qed.

Lemma i7 : 0 <= x -> 0 <= y ->
  proot r 2 (x * y) * proot r 3 x = proot r 6 (x ^+ 5) * proot r 2 y.
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
