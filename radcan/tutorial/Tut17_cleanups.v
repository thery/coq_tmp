From Stdlib Require Import Reals Lra.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import Rstruct PosRoot RootC RootR Syntax Radcan Refine Tactic RootRstd.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Section Cleanups.
Variables (F : numFieldType) (r : posroot F) (x y : F).

(* an inverse atom with exponent 3 is cancelled three times *)
(* raw: x != 0 *)
Lemma m1 : x != 0 -> x ^+ 3 / x ^+ 3 = 1.
Proof. move=> h. radcan. Show. exact: h. Qed.

Lemma m2 : x != 0 -> x * x / (x * x) = 1.
Proof. move=> h. radcan. Show. exact: h. Qed.

(* raw: x != 0, y != 0 *)
Lemma m3 : x != 0 -> y != 0 -> (x ^+ 3 * y) / (x ^+ 3 * y) = 1.
Proof. move=> h1 h2. radcan. Show. all: by []. Qed.

(* the same with a root somewhere *)
Lemma m3r : x != 0 -> y != 0 ->
  (x ^+ 3 * y) / (x ^+ 3 * y) = 1 + proot r 2 2 - proot r 2 2.
Proof. move=> h1 h2. radcan. all: by []. Qed.

Lemma m4 : x != 0 -> x ^+ 2 / x = x.
Proof. move=> h. radcan. exact: h. Qed.

Lemma m5 : x != 0 -> x / x ^+ 2 = 1 / x.
Proof. move=> h. radcan. exact: h. Qed.

(* rational coefficients in a radicand: x / 2 - 1 = (x - 2) / 2 *)
(* raw: 0 <= x - 2   refined: 2 <= x *)
Lemma m6 : 2 <= x -> proot r 2 (x / 2 - 1) ^+ 2 = x / 2 - 1.
Proof. move=> h. radcan. Show. exact: h. Qed.

(* inverse atoms are primitive with a positive leading coefficient *)
Lemma m7 : 1 / (2 * x + 2) = 1 / 2 * (1 / (x + 1)).
Proof. radcan. Qed.

Lemma m8 : 1 / (1 - x) = - (1 / (x - 1)).
Proof. radcan. Qed.

(* raw: x + 1 != 0   refined: x != -1 *)
Lemma m9 : x != -1 -> (2 * x + 2) / (x + 1) = 2.
Proof. move=> h. radcan. Show. exact: h. Qed.

Lemma m10 : x != -1 -> (2 * x + 2) / (3 * x + 3) = 2 / 3.
Proof. move=> h. radcan. exact: h. Qed.

(* the inverse of a product is the product of the inverses (no condition) *)
Lemma m11 : 1 / (x * y) = (1 / x) * (1 / y).
Proof. radcan. Qed.

(* a root common to all the terms of a denominator is inverted on its own *)
Lemma m12 : 1 / (proot r 2 2 * x + proot r 2 2) = proot r 2 2 / (2 * (x + 1)).
Proof. radcan. Qed.

(* exact division when the numerator has roots *)
Lemma m13 : x != -1 -> (proot r 2 2 * x + proot r 2 2) / (x + 1) = proot r 2 2.
Proof. move=> h. radcan. exact: h. Qed.

Lemma m14 : x != 0 -> x / (proot r 2 2 * x) = proot r 2 2 / 2.
Proof. move=> h. radcan. exact: h. Qed.
End Cleanups.

(* on Stdlib reals *)
Local Open Scope R_scope.
Lemma sm1 (x : R) : x <> 0 -> x ^ 3 / x ^ 3 = 1.
Proof. move=> h. radcan_Rstd. radcan. radcan_Rstd_back. exact: h. Qed.

Lemma sm2 (x : R) : 2 <= x -> sqrt (x / 2 - 1) ^ 2 = x / 2 - 1.
Proof. move=> h. radcan_Rstd. radcan. radcan_Rstd_back. lra. Qed.

Lemma sm3 (x : R) : x <> -1 -> (2 * x + 2) / (x + 1) = 2.
Proof. move=> h. radcan_Rstd. radcan. radcan_Rstd_back. lra. Qed.
