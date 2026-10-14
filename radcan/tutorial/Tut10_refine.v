From Stdlib Require Import Reals Lra.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import Rstruct PosRoot RootC RootR Syntax Radcan Refine Tactic RootRstd.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Section Generic.
Variables (F : numFieldType) (r : posroot F) (x y : F).

(* radcan refines the raw conditions 0 <= x + 1, 0 <= x - 1, x - 1 != 0 *)
Lemma f1 : 1 < x ->
  proot r 2 (x ^+ 2 - 1) / proot r 2 (x - 1) = proot r 2 (x + 1).
Proof. move=> x_gt1. radcan. Show. exact: x_gt1. Qed.

Lemma f2 : x != -1 -> x != 1 -> (x ^+ 2 - 1) / (x + 1) / (x - 1) = 1.
Proof. move=> h1 h2. radcan. Show. all: by []. Qed.

Lemma f3 : 1 <= x -> proot r 2 (x ^+ 2 - 1) = proot r 2 (x - 1) * proot r 2 (x + 1).
Proof. move=> h. radcan. exact: h. Qed.

(* a non-affine condition stays raw *)
Lemma f4 : 0 <= x * y + 1 ->
  proot r 2 (x * y + 1) * proot r 2 (x * y + 1) = x * y + 1.
Proof. move=> h. radcan. Show. Abort.
End Generic.

Local Open Scope R_scope.
Lemma sf1 (x : R) : 1 < x -> sqrt (x ^ 2 - 1) / sqrt (x - 1) = sqrt (x + 1).
Proof. move=> x_gt1. radcan_Rstd. radcan. Show. radcan_Rstd_back. lra. Qed.

(* several variables: refined since M8 (Tut15_refine2.v) *)
Section Multi.
Local Open Scope ring_scope.
Variables (F : numFieldType) (r : posroot F) (x y : F).
Lemma m1 : 0 <= x - y -> 0 <= x + y -> x - y != 0 ->
  proot r 2 (x ^+ 2 - y ^+ 2) / proot r 2 (x - y) = proot r 2 (x + y).
Proof.
move=> h1 h2 h3. radcan.
(* raw: 0 <= y + x,  0 <= -1 * y + x,  -1 * y + x != 0   *)
(* refined (M8): 0 <= x + y,  y < x                         *)
- exact: h2.
- by rewrite lt_def -subr_eq0 h3 -subr_ge0 h1.
Qed.
End Multi.
