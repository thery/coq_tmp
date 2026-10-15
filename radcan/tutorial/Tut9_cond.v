(******************************************************************************)
(* Tutorial 9: side conditions, raw (radcan_raw), closed by hand or by        *)
(* lra on Stdlib's R (radcan_Rstd_back).                                      *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import Rstruct PosRoot RootC RootR Syntax Radcan Tactic.
From Radcan Require Import RootRstd.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Section Generic.
Variables (F : numFieldType) (r : posroot F) (x y : F).
Local Notation "n .-proot" := (proot r n) (at level 2, format "n .-proot").
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).

Lemma c1 : 0 <= x -> \sqrt (x ^+ 2) = x.
Proof. move=> x_ge0. radcan_raw. exact: x_ge0. Qed.

Lemma c2 : 0 <= x -> \sqrt (4 * x) = 2 * \sqrt x.
Proof. move=> x_ge0. radcan_raw. exact: x_ge0. Qed.

Lemma c3 : 0 <= x -> 3.-proot x * 3.-proot (x ^+ 2) = x.
Proof. move=> x_ge0. radcan_raw. exact: x_ge0. Qed.

Lemma c4 : 0 <= x -> 0 <= y -> \sqrt (x * y) = \sqrt x * \sqrt y.
Proof. move=> x_ge0 y_ge0. radcan_raw. Show. all: by []. Qed.

(* three raw conditions, all consequences of 1 < x *)
Lemma c5 : 1 < x ->
  \sqrt (x ^+ 2 - 1) / \sqrt (x - 1) = \sqrt (x + 1).
Proof.
move=> x_gt1. radcan_raw. Show.
- by rewrite addr_ge0 // ltW // (lt_trans ltr01 x_gt1).
- by rewrite subr_ge0 ltW.
- by rewrite subr_eq0 gt_eqF.
Qed.

(* no root at all: rational-function cancellation, no root structure needed *)
Lemma c6 : x - 1 != 0 -> (x ^+ 2 - 1) / (x - 1) = x + 1.
Proof. move=> h. radcan_raw. exact: h. Qed.

Lemma c7 : x + 1 != 0 -> x - 1 != 0 -> (x ^+ 2 - 1) / (x + 1) / (x - 1) = 1.
Proof. move=> h1 h2. radcan_raw. Show. all: by []. Qed.

Lemma c8 : x != 0 -> x / x = 1.
Proof. move=> h. radcan_raw. exact: h. Qed.

Lemma c9 : x != 0 -> (x * y + x) / x = y + 1.
Proof. move=> h. radcan_raw. exact: h. Qed.
End Generic.

(* on Stdlib reals: radcan_Rstd_back + lra close the conditions *)
Local Open Scope R_scope.
Lemma sc5 (x : R) : 1 < x -> sqrt (x ^ 2 - 1) / sqrt (x - 1) = sqrt (x + 1).
Proof. move=> x_gt1. radcan_Rstd. radcan_raw. all: radcan_Rstd_back; lra. Qed.

Lemma sc6 (x : R) : 0 <= x -> sqrt (x ^ 3) = x * sqrt x.
Proof. move=> x_ge0. radcan_Rstd. radcan_raw. all: radcan_Rstd_back; lra. Qed.

Lemma sc7 (x : R) : x <> 1 -> (x ^ 2 - 1) / (x - 1) = x + 1.
Proof. move=> h. radcan_Rstd. radcan_raw. radcan_Rstd_back. lra. Qed.
