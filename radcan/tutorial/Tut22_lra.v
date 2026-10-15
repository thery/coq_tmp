(******************************************************************************)
(* Tutorial 22: radcan_lra on Stdlib reals (milestone M14).                   *)
(* radcan_lra = radcan_Rstd; radcan; then lra on each side condition; the     *)
(* conditions lra cannot prove are left in mathcomp notation.                 *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import Rstruct RootR Syntax Radcan Tactic RootRstd.
Local Open Scope R_scope.

Lemma l1 (x : R) : 1 < x -> sqrt (x ^ 2 - 1) / sqrt (x - 1) = sqrt (x + 1).
Proof. move=> h. radcan_lra. Qed.

Lemma l2 (x : R) : 1 <= x <= 3 ->
  sqrt (x - 1) * sqrt (3 - x) = sqrt (- x ^ 2 + 4 * x - 3).
Proof. move=> h. radcan_lra. Qed.

Lemma l3 : sqrt 12 - sqrt 3 = sqrt 3.
Proof. radcan_lra. Qed.

(* the condition x ^+ 2 != 2 is closed by lra from the hypothesis *)
Lemma l4 (x : R) : x ^ 2 <> 2 -> 1 / (x + sqrt 2) = (x - sqrt 2) / (x ^ 2 - 2).
Proof. move=> h. radcan_lra. Qed.

(* two conditions, both closed by lra from the hypotheses *)
Lemma l5 (x : R) : 0 <= x -> x <> 1 ->
  1 / (1 + sqrt x) = (1 - sqrt x) / (1 - x).
Proof. move=> h1 h2. radcan_lra. Qed.

(* without a hypothesis the condition 0 <= x is left as a goal *)
Goal forall x : R, sqrt (x ^ 2) = x.
Proof. move=> x. radcan_lra. Show. Abort.
