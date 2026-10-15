(******************************************************************************)
(* Tutorial 24: a variable monomial taken out of a denominator (M18).         *)
(* d = g * d' with g the monomial common to all the terms of d (checked by    *)
(* normalisation), d^-1 = g^-1 * d'^-1: 1/(x^2 + x) = 1/x * 1/(x + 1).        *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import Rstruct PosRoot RootR Syntax Radcan Tactic.
From Radcan Require Import RootRstd.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Section Denom.
Variables (F : numFieldType) (r : posroot F) (x y : F).
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).

(* the inverse of a product is the product of the inverses: no condition *)
Lemma t1 : 1 / (x ^+ 2 + x) = 1 / x * (1 / (x + 1)).
Proof. radcan. Qed.

Lemma t2 : 1 / (x * y + x) = 1 / x * (1 / (y + 1)).
Proof. radcan. Qed.

(* exponents: x ^+ 2 is taken out *)
Lemma t3 : 1 / (x ^+ 3 + 2 * x ^+ 2) = 1 / x ^+ 2 * (1 / (x + 2)).
Proof. radcan. Qed.

(* cancellation of x + 1 only *)
(* raw: x + 1 != 0   refined: x != -1 *)
Lemma t4 : x != -1 -> (x + 1) / (x ^+ 2 + x) = 1 / x.
Proof. move=> h. radcan. exact: h. Qed.

(* raw: x != 0, y != 0 *)
Lemma t5 : x != 0 -> y != 0 ->
  (x ^+ 2 * y) / (x ^+ 3 * y + x ^+ 2 * y) = 1 / (x + 1).
Proof. move=> hx hy. radcan. all: by []. Qed.

(* with roots: the monomial x, then the root monomial sqrt 2 *)
Lemma t6 : \sqrt 2 / (x ^+ 2 * \sqrt 2 + x) =
  \sqrt 2 / x * (1 / (\sqrt 2 * x + 1)).
Proof. radcan. Qed.

Lemma t7 : \sqrt 2 / (x ^+ 2 * \sqrt 2 + x * \sqrt 2) = 1 / x * (1 / (x + 1)).
Proof. radcan. Qed.

(* a common inverse atom (root-free path) *)
Lemma t8 : 1 / (x / (y + 1) + 1 / (y + 1)) = (y + 1) / (x + 1).
Proof. radcan. Qed.
End Denom.

(* on Stdlib reals *)
Local Open Scope R_scope.
Lemma st1 (x : R) : x <> -1 -> (x + 1) / (x ^ 2 + x) = 1 / x.
Proof. move=> h. radcan_lra. Qed.

Lemma st2 (x y : R) : 1 / (x * y + x) = 1 / x * (1 / (y + 1)).
Proof. radcan_lra. Qed.

Print Assumptions t6.  (* Closed under the global context *)
