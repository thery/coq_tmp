(******************************************************************************)
(* Tutorial 15: refined conditions with several variables.                    *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import Rstruct PosRoot RootC RootR Syntax Radcan Refine.
From Radcan Require Import Tactic RootRstd.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Section Multi.
Variables (F : numFieldType) (r : posroot F) (x y : F).

(* raw: 0 <= y + x, 0 <= -1 * y + x, -1 * y + x != 0
   refined: 0 <= x + y, y < x *)
Lemma g1 : 0 <= x + y -> y < x ->
  proot r 2 (x ^+ 2 - y ^+ 2) / proot r 2 (x - y) = proot r 2 (x + y).
Proof. move=> h1 h2. radcan. Show. all: by []. Qed.

(* the same with y <= x and x != y: y < x is lt_def *)
Lemma g2 : 0 <= x + y -> y <= x -> x != y ->
  proot r 2 (x ^+ 2 - y ^+ 2) / proot r 2 (x - y) = proot r 2 (x + y).
Proof. move=> h1 h2 h3. radcan. - exact: h1. - by rewrite lt_def h3 h2. Qed.

(* raw: 0 <= 2 * x - 2 * y   refined: y <= x  (divided by 2) *)
Lemma g3 : y <= x -> proot r 2 (2 * x - 2 * y) ^+ 2 = 2 * x - 2 * y.
Proof. move=> h. radcan. Show. exact: h. Qed.

(* a constant stays: raw 0 <= 2 * x - 2 * y + 1   refined: 2 * y - 1 <= 2 * x *)
Lemma g4 : 2 * y - 1 <= 2 * x ->
  proot r 2 (2 * x - 2 * y + 1) ^+ 2 = 2 * x - 2 * y + 1.
Proof. move=> h. radcan. Show. exact: h. Qed.

(* not affine: the constant goes to the other side *)
(* raw: 0 <= x * y + 1   refined: -1 <= x * y *)
Lemma g5 : -1 <= x * y ->
  proot r 2 (x * y + 1) * proot r 2 (x * y + 1) = x * y + 1.
Proof. move=> h. radcan. Show. exact: h. Qed.

(* raw: 0 <= x ^+ 2 - 1   refined: 1 <= x ^+ 2 *)
Lemma g6 : 1 <= x ^+ 2 -> proot r 2 (x ^+ 2 - 1) ^+ 2 = x ^+ 2 - 1.
Proof. move=> h. radcan. Show. exact: h. Qed.

(* raw: x ^+ 2 - 4 != 0   refined: x ^+ 2 != 4 *)
Lemma g7 : x ^+ 2 != 4 -> (x ^+ 2 - 4) / (x ^+ 2 - 4) = 1.
Proof. move=> h. radcan. Show. exact: h. Qed.

(* x * y != 0 gives x != 0 and y != 0 (see also refine_ex13) *)
Lemma g8 : x != 0 -> y != 0 -> (x * y) / (x * y) = 1.
Proof. move=> h1 h2. radcan. Show. all: by []. Qed.

(* the normaliser expands (x - 1) * (x + 1): no factorisation is tried *)
(* raw: x ^+ 2 - 1 != 0   refined: x ^+ 2 != 1 *)
Lemma g9 : x ^+ 2 != 1 -> (x - 1) * (x + 1) / ((x - 1) * (x + 1)) = 1.
Proof. move=> h. radcan. Show. exact: h. Qed.
End Multi.

(* on Stdlib reals the refined conditions are closed by lra *)
Local Open Scope R_scope.
Lemma sg1 (x y : R) : 0 <= x + y -> y < x ->
  sqrt (x ^ 2 - y ^ 2) / sqrt (x - y) = sqrt (x + y).
Proof. move=> h1 h2. radcan_Rstd. radcan. all: radcan_Rstd_back; lra. Qed.
