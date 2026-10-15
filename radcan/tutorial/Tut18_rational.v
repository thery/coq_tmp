From Stdlib Require Import Reals Lra.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import Rstruct PosRoot RootC RootR Syntax Radcan.
From Radcan Require Import Refine Tactic RootRstd.
Import Order.TTheory GRing.Theory Num.Theory.

(* Part 18: denominators mixing variables and roots (milestone M11).        *)
(* 1 / d = u / E with d * u = E checked by normalisation, E root-free;     *)
(* the new condition is E != 0.                                            *)

Local Open Scope ring_scope.
Section Rational.
Variables (F : numFieldType) (r : posroot F) (x y : F).
Local Notation "n .-proot" := (proot r n) (at level 2, format "n .-proot").
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).

(* the paper's (1) as a quotient *)
(* raw: 0 <= x, 0 <= y, -1 * y + x != 0   refined: 0 <= x, 0 <= y, x != y *)
Lemma q1 : 0 <= x -> 0 <= y -> x != y ->
  (x - y) / (\sqrt x + \sqrt y) = \sqrt x - \sqrt y.
Proof. move=> hx hy hxy. radcan. all: by []. Qed.

(* refined: 0 <= x, x != 1 *)
Lemma q2 : 0 <= x -> x != 1 -> 1 / (1 + \sqrt x) = (1 - \sqrt x) / (1 - x).
Proof. move=> hx h1. radcan. all: by []. Qed.

(* refined: x ^+ 2 != 2 *)
Lemma q3 : x ^+ 2 != 2 -> 1 / (x + \sqrt 2) = (x - \sqrt 2) / (x ^+ 2 - 2).
Proof. move=> h. radcan. exact: h. Qed.

(* the paper's (3), with the right E (108 x, not 54 x) *)
Lemma q4 : 108 * x + 12 * x ^+ 2 + 18 * x ^+ 3 + x ^+ 6 != 6 * x ^+ 4 - 73 ->
  1 / (x + \sqrt 2 + 3.-proot 9) =
  (- (x + \sqrt 2) * 3.-proot 9 + 3 * 3.-proot 3 +
     (x ^+ 2 + 2 * \sqrt 2 * x + 2)) *
  (x ^+ 3 + 6 * x + 9 - (3 * x ^+ 2 + 2) * \sqrt 2) /
  (x ^+ 6 - 6 * x ^+ 4 + 18 * x ^+ 3 + 12 * x ^+ 2 + 108 * x + 73).
Proof. move=> h. radcan. exact: h. Qed.

Lemma q5 : 0 <= x -> 0 <= y -> x != y ->
  (\sqrt x + \sqrt y) / (\sqrt x - \sqrt y) =
  (x + y + 2 * \sqrt x * \sqrt y) / (x - y).
Proof. move=> hx hy hxy. radcan. all: by []. Qed.
End Rational.

(* on Stdlib reals *)
Local Open Scope R_scope.
Lemma sq1 (x y : R) : 0 <= x -> 0 <= y -> x <> y ->
  (x - y) / (sqrt x + sqrt y) = sqrt x - sqrt y.
Proof. move=> hx hy hxy. radcan_Rstd. radcan. all: radcan_Rstd_back; lra. Qed.

Lemma sq2 (x : R) : x ^ 2 <> 2 -> 1 / (x + sqrt 2) = (x - sqrt 2) / (x ^ 2 - 2).
Proof. move=> h. radcan_Rstd. radcan. radcan_Rstd_back. lra. Qed.
