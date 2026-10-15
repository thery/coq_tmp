(******************************************************************************)
(* Tutorial 10: refined side conditions (radcan, Refine.v).                   *)
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

(* radcan refines the raw conditions 0 <= x + 1, 0 <= x - 1, x - 1 != 0 *)
Lemma f1 : 1 < x ->
  \sqrt (x ^+ 2 - 1) / \sqrt (x - 1) = \sqrt (x + 1).
Proof. move=> x_gt1. radcan. Show. exact: x_gt1. Qed.

Lemma f2 : x != -1 -> x != 1 -> (x ^+ 2 - 1) / (x + 1) / (x - 1) = 1.
Proof. move=> h1 h2. radcan. Show. all: by []. Qed.

Lemma f3 : 1 <= x ->
  \sqrt (x ^+ 2 - 1) = \sqrt (x - 1) * \sqrt (x + 1).
Proof. move=> h. radcan. exact: h. Qed.

(* a non-affine condition stays raw *)
Lemma f4 : 0 <= x * y + 1 ->
  \sqrt (x * y + 1) * \sqrt (x * y + 1) = x * y + 1.
Proof. move=> h. radcan. Show. Abort.
End Generic.

Local Open Scope R_scope.
Lemma sf1 (x : R) : 1 < x -> sqrt (x ^ 2 - 1) / sqrt (x - 1) = sqrt (x + 1).
Proof. move=> x_gt1. radcan_Rstd. radcan. Show. radcan_Rstd_back. lra. Qed.

(* several variables (more in Tut15_refine2.v) *)
Section Multi.
Local Open Scope ring_scope.
Variables (F : numFieldType) (r : posroot F) (x y : F).
Local Notation "n .-proot" := (proot r n) (at level 2, format "n .-proot").
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).
Lemma m1 : 0 <= x - y -> 0 <= x + y -> x - y != 0 ->
  \sqrt (x ^+ 2 - y ^+ 2) / \sqrt (x - y) = \sqrt (x + y).
Proof.
move=> h1 h2 h3. radcan.
(* raw: 0 <= y + x, 0 <= -1 * y + x, -1 * y + x != 0
   refined: 0 <= x + y, y < x *)
- exact: h2.
- by rewrite lt_def -subr_eq0 h3 -subr_ge0 h1.
Qed.
End Multi.
