(******************************************************************************)
(* Tutorial 19: intervals and combinations of bounds (milestone M12).         *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import Rstruct PosRoot RootC RootR Syntax Radcan Refine.
From Radcan Require Import Tactic RootRstd.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Section Bounds.
Variables (F : numFieldType) (r : posroot F) (x y : F).
Local Notation "n .-proot" := (proot r n) (at level 2, format "n .-proot").
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).

(* raw: 0 <= x - 1, 0 <= -1 * x + 3   refined: 1 <= x <= 3 *)
Lemma h1 : 1 <= x <= 3 ->
  \sqrt (x - 1) * \sqrt (3 - x) = \sqrt (- x ^+ 2 + 4 * x - 3).
Proof. move=> h. radcan. Show. exact: h. Qed.

(* a strict side: raw 0 <= x - 1, 0 <= -1 * x + 3, x - 3 != 0
   refined: 1 <= x < 3 *)
Lemma h2 : 1 <= x < 3 ->
  \sqrt (x - 1) ^+ 2 * \sqrt (3 - x) ^+ 2 / (3 - x) = x - 1.
Proof. move=> h. radcan. Show. exact: h. Qed.

(* 0 <= 4 - x follows from x <= 3: raw 0 <= x - 1, 0 <= 3 - x, 0 <= 4 - x
   refined: 1 <= x <= 3 *)
Lemma h3 : 1 <= x <= 3 ->
  \sqrt (x - 1) ^+ 2 + \sqrt (3 - x) ^+ 2 + \sqrt (4 - x) ^+ 2
  = 6 - x.
Proof. move=> h. radcan. Show. exact: h. Qed.

(* combinations: x + y - 2 = (x - 1) + (y - 2) + 1, so 0 < x + y - 2
   follows from 1 <= x and 2 <= y
   raw: 0 <= y + (x - 2), y + (x - 2) != 0, 0 <= x - 1, 0 <= y - 2
   refined: 1 <= x, 2 <= y *)
Lemma h4 : 1 <= x -> 2 <= y ->
  \sqrt (x + y - 2) / \sqrt (x + y - 2) * \sqrt (x - 1)
  * \sqrt (y - 2) = \sqrt ((x - 1) * (y - 2)).
Proof. move=> hx hy. radcan. Show. all: by []. Qed.

(* only true combinations: 1 <= x and 2 <= y do not give 3 < x + y *)
(* refined: 1 <= x, 2 <= y, 3 < x + y *)
Lemma h5 : 1 <= x -> 2 <= y -> 3 < x + y ->
  \sqrt (x + y - 3) / \sqrt (x + y - 3) * \sqrt (x - 1)
  * \sqrt (y - 2) = \sqrt ((x - 1) * (y - 2)).
Proof. move=> hx hy hxy. radcan. Show. all: by []. Qed.

(* contradictory bounds are kept as they are: the goal 3 <= x <= 1 *)
(* cannot be proved                                                   *)
Goal \sqrt (x - 3) * \sqrt (1 - x) = \sqrt (- x ^+ 2 + 4 * x - 3).
Proof. radcan. Show. Abort.
End Bounds.

(* on Stdlib reals the interval is split, each side closed by lra *)
Local Open Scope R_scope.
Lemma sh1 (x : R) : 1 <= x <= 3 ->
  sqrt (x - 1) * sqrt (3 - x) = sqrt (- x ^ 2 + 4 * x - 3).
Proof.
move=> h. radcan_Rstd. radcan. Show.
all: radcan_Rstd_back; lra.
Qed.
