(******************************************************************************)
(* Tutorial 31: omega_rw on roots of fractions (OmegaPass.v, omega_frac).     *)
(* For a radicand P / Q with a variable (read as in Frac's nd), omega_rw      *)
(* tests the signs of P and Q apart (last monomial negative, as for a plain   *)
(* radicand) and, for any index n,                                            *)
(*   P negative:     n.-root (P / Q) = n.-root (- P / Q) * omega_n            *)
(*                   under 0 <= - P, 0 <= Q                                   *)
(*   Q negative:     n.-root (P / Q) = n.-root (P / - Q) * omega_n            *)
(*                   under 0 <= P, 0 <= - Q                                   *)
(*   both negative:  n.-root (P / Q) = n.-root (- P / - Q), no condition      *)
(* frac_split then splits the new fraction under the same conditions, so the  *)
(* collected conditions agree (before, 4.-root ((1 - x) / y) gave both        *)
(* 0 <= 1 - x and 0 <= x - 1).  omega_n is explicit for n = 2, 3, 4, 6, 12,   *)
(* n.-root (-1) otherwise.  radcan runs omega_rw in its pre-pass on C, or     *)
(* with a smallroot in the context (Tutorial 29).                             *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts RootC Syntax.
From Radcan Require Import Radcan Refine Tactic OmegaRoot OmegaC Prepass.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Section Complex.
Variables (C : numClosedFieldType) (x y : C).

(* numerator negative; refined: 1 <= x, 0 <= y *)
Lemma c1 : 1 <= x -> 0 < y ->
  4.-root ((1 - x) / y) = 4.-root (x - 1) / 4.-root y * 4.-root (-1).
Proof. move=> hx hy. radcan; [exact: hx | exact: ltW]. Qed.

(* a negative constant numerator, n = 2; refined: 0 <= x *)
Lemma c2 : 0 < x -> 2.-root (-4 / x) = 2 * 2.-root (-1) / 2.-root x.
Proof. move=> h. radcan. exact: ltW. Qed.

(* the cube root of Tutorial 29 (omega_3 explicit); refined: 0 <= x *)
Lemma c3 : 0 < x ->
  3.-root (-8 / x) = (1 + 2.-root 3 * 2.-root (-1)) / 3.-root x.
Proof. move=> h. radcan. exact: ltW. Qed.

(* denominator negative; refined: 0 <= x, 1 <= y *)
Lemma c4 : 0 <= x -> 1 <= y ->
  4.-root (x / (1 - y)) = 4.-root x / 4.-root (y - 1) * 4.-root (-1).
Proof. move=> hx hy. radcan; [exact: hx | exact: hy]. Qed.

(* both negative: no omega_n; refined: 0 <= x, 1 <= y *)
Lemma c5 : 0 <= x -> 1 < y ->
  2.-root (- x / (1 - y)) = 2.-root x / 2.-root (y - 1).
Proof. move=> hx hy. radcan; [exact: hx | exact: ltW]. Qed.

(* a constant denominator; refined: 1 <= x *)
Lemma c6 : 1 <= x ->
  3.-root ((1 - x) / 8) = 3.-root (x - 1) / 2 * 3.-root (-1).
Proof. move=> h. radcan. exact: h. Qed.
End Complex.

Section Generic.
Variables (F : numFieldType) (r : posroot F) (w : negroot r) (x y : F).
Local Notation "n .-proot" := (proot r n) (at level 2, format "n .-proot").
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).
Hypothesis ov : smallroot w.

(* refined: 1 <= x, 0 <= y *)
Lemma g1 : 1 <= x -> 0 < y ->
  4.-proot ((1 - x) / y) = 4.-proot (x - 1) / 4.-proot y * 4.-proot (-1).
Proof. move=> hx hy. radcan; [exact: hx | exact: ltW]. Qed.

(* refined: 0 <= x *)
Lemma g2 : 0 < x -> \sqrt (-4 / x) = 2 * \sqrt (-1) / \sqrt x.
Proof. move=> h. radcan. exact: ltW. Qed.

(* the radicand is -1 for x <> 1: the denominator is flipped, then         *)
(* 4.-root (x - 1) / 4.-root (x - 1) cancels; refined: x != 1 (1 <= x)    *)
Lemma g3 : 1 < x -> 4.-proot ((x - 1) / (1 - x)) = 4.-proot (-1).
Proof. by move=> h; radcan; rewrite gt_eqF. Qed.
End Generic.
