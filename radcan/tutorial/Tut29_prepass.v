(******************************************************************************)
(* Tutorial 29: the composed pre-pass (Prepass.v).                            *)
(* When the plain check fails, radcan rewrites both sides with               *)
(*   prepass = omega_rw o denest_rwc o frac_split                             *)
(* (roots of fractions split, Tutorial 26; square roots denested, Tutorial    *)
(* 25; n.-root of negative radicands through omega_n, Tutorial 28, only with  *)
(* a smallroot), iterated until nothing changes (at most radcan_fuel = 4      *)
(* rounds), then runs the checker of the mode.  The conditions of every pass  *)
(* are collected and refined.  The goals below need two passes together.      *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts RootC RootR RealRoot Syntax.
From Radcan Require Import Radcan Refine Tactic OmegaRoot OmegaC Prepass.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Section Generic.
Variables (F : numFieldType) (r : posroot F) (x : F).
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).

(* fractions, then denesting of sqrt (3 + 2 sqrt 2)                         *)
(* refined: 0 <= x (the checker, 1 / sqrt x); 0 <= 3 + 2 sqrt 2 from       *)
(* frac_split is dropped (sign certificate, SignCert.v)                    *)
Lemma p1 : 0 <= x -> \sqrt ((3 + 2 * \sqrt 2) / x) = (1 + \sqrt 2) / \sqrt x.
Proof.
move=> h. Fail radcan_plain_gen true. Time radcan; exact: h.
Qed.

(* fractions, then denesting with a variable                               *)
(* refined: 1 <= x; 0 <= x + 2 sqrt (x - 1) (frac_split) follows from it    *)
Lemma p2 : 1 <= x ->
  \sqrt ((x + 2 * \sqrt (x - 1)) / 4) = (1 + \sqrt (x - 1)) / 2.
Proof.
move=> h. Time radcan; exact: h.
Qed.

(* denesting creates fractions: sqrt (x + sqrt (x^2 - 4)) is              *)
(* sqrt ((x + 2) / 2) + sqrt ((x - 2) / 2), split at the second round      *)
Lemma p3 : 2 <= x ->
  \sqrt (x + \sqrt (x ^+ 2 - 4)) * \sqrt 2 = \sqrt (x + 2) + \sqrt (x - 2).
Proof. move=> h. Time radcan. exact: h. Qed.

(* a constant fraction: sqrt (3 / 2 + sqrt 2) = 1 + sqrt 2 / 2 *)
Lemma p4 : \sqrt (3 / 2 + \sqrt 2) * \sqrt 2 = \sqrt 2 + 1.
Proof. Fail radcan_plain_gen true. Time by radcan. Qed.

(* the pre-pass alone: (sqrt (3 + 2 sqrt 2) * sqrt x ^-1) denested *)
Eval vm_compute in
  prepass false false 4
    (RRootE 2 (RMul (RAdd (RCst 3) (RMul (RCst 2) (RRoot 2 2)))
                    (RInv (RVar 0)))).
End Generic.

(* omega_rw runs first (with a smallroot): n.-root (-8 / x) becomes        *)
(* n.-root (8 / x) * omega_n, then frac_split splits 8 / x                   *)
Section Omega.
Variables (F : numFieldType) (r : posroot F) (w : negroot r) (x : F).
Hypothesis ov : smallroot w.

(* refined: 0 <= x (0 <= x^-1 is read as 0 <= x) *)
Lemma o1 : 0 < x ->
  proot r 3 (-8 / x) = (1 + proot r 2 3 * proot r 2 (-1)) / proot r 3 x.
Proof. move=> h. Time radcan. all: by rewrite ?invr_ge0 ltW. Qed.
End Omega.

Section Complex.
Variables (C : numClosedFieldType) (x : C).

Lemma c1 : 0 < x ->
  3.-root (-8 / x) = (1 + 2.-root 3 * 2.-root (-1)) / 3.-root x.
Proof. move=> h. Time radcan. all: by rewrite ?invr_ge0 ltW. Qed.
End Complex.

(* Limitation: omega_rw does not see the sign of a fraction radicand with  *)
(* a variable, so 4.-root ((1 - x) / y) is first split by frac_split under *)
(* 0 <= 1 - x, then 4.-root (1 - x) rewritten under 0 <= x - 1: the goal  *)
(* is proved only for x = 1                                                *)
