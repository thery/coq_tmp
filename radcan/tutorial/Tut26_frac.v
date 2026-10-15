(******************************************************************************)
(* Tutorial 26 (M20): roots of fractions, the paper's rule (i):               *)
(*   (P / Q)^(1/n) = P^(1/n) / Q^(1/n)  under 0 <= P and 0 <= Q.              *)
(* Frac.v: frac_split rewrites every root of a fraction with a variable into  *)
(* the quotient of the roots, recording 0 <= P, 0 <= Q (nothing for an odd    *)
(* root on a real field); radcan_eq_frac* then run the usual checkers.        *)
(* radcan runs the plain check first and, when it fails, frac_split and the *)
(* checker of the mode again.                                               *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts RootC RootR RealRoot Syntax.
From Radcan Require Import Radcan Refine Tactic OddRoot NegRootC AbsRoot Frac.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* radcan_with_gen of Tactic.v, with frac_split before the checker *)
(* radcan falls back to frac_split when the plain check fails *)

Section Generic.
Variables (F : numFieldType) (r : posroot F) (x y z : F).
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).

(* plain radcan fails: the radicand (x - 1) / (x + 2) is one opaque atom   *)
(* raw: 0 <= x - 1, 0 <= x + 2 (twice)   refined: 1 <= x                    *)
Lemma f1 : 1 <= x -> \sqrt ((x - 1) / (x + 2)) = \sqrt (x - 1) / \sqrt (x + 2).
Proof. move=> h. Time radcan. exact: h. Qed.

Lemma f1r : 0 <= x - 1 -> 0 <= x + 2 ->
  \sqrt ((x - 1) / (x + 2)) = \sqrt (x - 1) / \sqrt (x + 2).
Proof. move=> h1 h2. radcan_raw. all: by []. Qed.

(* refined: 0 <= x, 0 < y *)
Lemma f2 : 0 <= x -> 0 < y -> \sqrt (x / y) * \sqrt y = \sqrt x.
Proof. move=> hx hy. Time radcan. all: by []. Qed.

(* a lone inverse: 1 / x is 1 * x^-1; refined: 0 <= x *)
Lemma f3 : 0 <= x -> \sqrt (1 / x) = 1 / \sqrt x.
Proof. move=> h. Time radcan. exact: h. Qed.

Lemma f3b : 0 <= x -> \sqrt (x^-1) = (\sqrt x)^-1.
Proof. move=> h. radcan. exact: h. Qed.

(* the paper's (9): ((x^2 - 1) / (x + 2))^(1/2) / (x^2 + 3x + 2)^(1/3)     *)
(* refined: 1 <= x (1 <= x ^+ 2 follows from it and is dropped)            *)
Lemma f4 : 1 <= x ->
  \sqrt ((x ^+ 2 - 1) / (x + 2)) / proot r 3 (x ^+ 2 + 3 * x + 2) =
  \sqrt (x - 1) * \sqrt (x + 1) / \sqrt (x + 2) /
  (proot r 3 (x + 1) * proot r 3 (x + 2)).
Proof.
move=> h. Time radcan; exact: h.
Qed.

(* products and powers in the fraction, roots in the radicand *)
Lemma f5 : 0 <= x -> 0 <= y -> 0 <= z ->
  \sqrt (x * y / (z * x ^+ 2)) = \sqrt y / (\sqrt z * \sqrt x).
Proof.
move=> hx hy hz. Time radcan.
all: by rewrite ?mulr_ge0 ?exprn_ge0.
Qed.

Lemma f6 : 0 <= x -> 0 <= y ->
  \sqrt ((x / y) ^+ 3) = \sqrt x * x / (\sqrt y * y).
Proof. move=> hx hy. Time radcan. all: by rewrite ?exprn_ge0. Qed.

Lemma f7 : 0 <= x -> 0 <= y ->
  \sqrt (\sqrt (x / y)) = \sqrt (\sqrt x) / \sqrt (\sqrt y).
Proof. move=> hx hy. Time radcan. all: by rewrite ?proot_ge0. Qed.

(* constant fractions are left to plain radcan, unchanged *)
Lemma f8 : \sqrt (2 / 3) = \sqrt 6 / 3.
Proof. by radcan. Qed.
End Generic.

Section Real.
Variables (R : rcfType) (x y : R).

(* real mode: odd roots split with no condition from frac_split *)
Lemma g1 : rootR 3 (x / 8) = rootR 3 x / 2.
Proof. Time by radcan. Qed.

(* 0 <= y comes from the checker (the inverse of rootR 3 y), not from     *)
(* frac_split                                                              *)
Lemma g2 : 0 <= y -> rootR 3 (x / y) = rootR 3 x / rootR 3 y.
Proof. move=> h. Time radcan. exact: h. Qed.

(* refined: 1 <= x *)
Lemma g3 : 1 <= x ->
  rootR 2 ((x - 1) / (x + 2)) = rootR 2 (x - 1) / rootR 2 (x + 2).
Proof. move=> h. Time radcan. exact: h. Qed.
End Real.

Section Complex.
Variables (C : numClosedFieldType) (x : C).

(* refined: -1 <= x *)
Lemma h1 : -1 <= x -> 2.-root ((x + 1) / 4) = 2.-root (x + 1) / 2.
Proof. move=> h. Time radcan. exact: h. Qed.
End Complex.
