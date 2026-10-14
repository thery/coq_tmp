(******************************************************************************)
(* Tutorial 14: polynomial gcd and square-free decomposition of the           *)
(* radicands: x^2 + 2x + 1 is read as (x + 1)^2 (Yun), the basis is made      *)
(* coprime (Collins), rational functions cancel through a gcd.  Every         *)
(* decomposition is checked by multiplication.                                *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import Rstruct PosRoot RootC RootR Syntax Radcan Refine.
From Radcan Require Import Tactic RootRstd.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Section Generic.
Variables (F : numFieldType) (r : posroot F) (x y : F).

(* raw: 0 <= x + 1   refined: -1 <= x *)
Lemma g1 : -1 <= x -> proot r 2 (x ^+ 2 + 2 * x + 1) = x + 1.
Proof. move=> h. radcan. Show. exact: h. Qed.

(* raw: 0 <= x - 1   refined: 1 <= x *)
Lemma g2 : 1 <= x ->
  proot r 2 (x ^+ 3 - 3 * x ^+ 2 + 3 * x - 1) = (x - 1) * proot r 2 (x - 1).
Proof. move=> h. radcan. Show. exact: h. Qed.

(* (x^2 - 1)^2: raw 0 <= x ^+ 2 - 1, refined 1 <= x ^+ 2 *)
Lemma g3 : 1 <= x ^+ 2 -> proot r 2 (x ^+ 4 - 2 * x ^+ 2 + 1) = x ^+ 2 - 1.
Proof. move=> h. radcan. Show. exact: h. Qed.

Lemma g4 : -1 <= x ->
  proot r 2 (x ^+ 2 + 2 * x + 1) * proot r 2 (x + 1) =
  (x + 1) * proot r 2 (x + 1).
Proof. move=> h. radcan. exact: h. Qed.

Lemma g5 : -1 <= x ->
  proot r 2 (2 * x ^+ 2 + 4 * x + 2) = (x + 1) * proot r 2 2.
Proof. move=> h. radcan. exact: h. Qed.

(* the same base under a cube root *)
Lemma g6 : -1 <= x -> proot r 3 (x ^+ 3 + 3 * x ^+ 2 + 3 * x + 1) = x + 1.
Proof. move=> h. radcan. exact: h. Qed.

(* several variables: the condition is 0 <= x + y *)
Lemma g7 : 0 <= x + y -> proot r 2 (x ^+ 2 + 2 * x * y + y ^+ 2) = x + y.
Proof. move=> h. radcan. Show. first [exact: h | by rewrite addrC]. Qed.

(* y (x + 1)^2: two conditions, 0 <= y and -1 <= x *)
Lemma g8 : 0 <= y -> -1 <= x ->
  proot r 2 (y * x ^+ 2 + 2 * x * y + y) = (x + 1) * proot r 2 y.
Proof. move=> hy hx. radcan. Show. all: by []. Qed.

(* no root: cancellation through gcd (x^2 - 1, x^2 + 2x + 1) = x + 1 *)
(* raw: x + 1 != 0   refined: x != -1 *)
Lemma g9 : x != -1 ->
  (x ^+ 2 - 1) / (x ^+ 2 + 2 * x + 1) = (x - 1) / (x + 1).
Proof. move=> h. radcan. Show. exact: h. Qed.

Lemma g10 : x + y != 0 ->
  (x ^+ 2 - y ^+ 2) / (x ^+ 2 + 2 * x * y + y ^+ 2) = (x - y) / (x + y).
Proof. move=> h. radcan. Show. first [exact: h | by rewrite addrC]. Qed.
End Generic.

Local Open Scope R_scope.
Lemma sg1 (x : R) : -1 <= x -> sqrt (x ^ 2 + 2 * x + 1) = x + 1.
Proof. move=> h. radcan_Rstd. radcan. radcan_Rstd_back. lra. Qed.

Lemma sg2 (x : R) : x <> -1 ->
  (x ^ 2 - 1) / (x ^ 2 + 2 * x + 1) = (x - 1) / (x + 1).
Proof. move=> h. radcan_Rstd. radcan. radcan_Rstd_back. lra. Qed.

Lemma sg3 (x y : R) : 0 <= x + y -> sqrt (x ^ 2 + 2 * x * y + y ^ 2) = x + y.
Proof. move=> h. radcan_Rstd. radcan. radcan_Rstd_back. lra. Qed.
