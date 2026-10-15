(******************************************************************************)
(* Tutorial 38: radcan_trig, trigonometric identities on Stdlib's reals.     *)
(* Tutorial 35 proved IMO 1963 by hand: go to C = R[i] with                  *)
(* E x = cos x + i sin x, write cos and sin through E, the angles k PI / n   *)
(* as powers of n.-root (-1), run radcan, come back to R.  radcan_trig       *)
(* (trig/TrigTac.v) does it for any goal built from numerals, variables,     *)
(* + - * / ^, sqrt of numerals, cos sin tan of                               *)
(* (integer combination of variables) + (rational multiple of PI):           *)
(*  1. tan unfolded, denominators cleared on R by field_simplify_eq: its     *)
(*     conditions p <> 0 are stated on R (cos x <> 0, ...)                   *)
(*  2. trig_push: %:C through the operations, cos x and sin x as             *)
(*     (E x +- (E x)^-1) / (2 or 2 i), i = 2.-root (-1)                      *)
(*  3. trig_angles: E (a + b) = E a * E b, E (k a) = E a ^+ k, E (- a) =     *)
(*     (E a)^-1, E (k PI / n) = n.-root (-1) ^+ k                            *)
(*  4. trig_clear: each E x becomes a variable u with u != 0, and both sides *)
(*     are multiplied by its largest negative power: radcan then compares    *)
(*     polynomials in u, not Laurent polynomials (on which it fails)         *)
(*  5. radcan (roots of unity: merging, cyclotomic reduction, square roots   *)
(*     of numerals through Gauss sums); the conditions u != 0 are closed     *)
(*  6. the conditions of step 1 are closed from the hypotheses (equal, or    *)
(*     opposite, or a factor of one: checked by steps 2-5), from the sign of *)
(*     cos and sin on closed angles, or left to the user                     *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import Syntax Tactic.
From RadcanTrig Require Import TrigTac.
Import GRing.Theory.

Local Open Scope R_scope.

(* one call *)
Lemma cos3 x : cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x.
Proof. radcan_trig. Qed.

(* the steps, one by one *)
Lemma cos3_steps x : cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x.
Proof.
field_simplify_eq.
apply: trig_realC; trig_push.
(* (E (3 * x) + (E (3 * x))^-1) / 2 = ... ((E x + (E x)^-1) / 2) ... *)
trig_angles.
(* E (3 * x) is now E x ^+ 3 *)
trig_clear.
(* u := E x, hu : u != 0, both sides multiplied by u ^+ 3 *)
radcan.
(* the condition u != 0 *)
by [].
Qed.

(* special values: E (PI / 5) = 5.-root (-1), sqrt 5 through Gauss sums *)
Lemma cos_PI5 : cos (PI / 5) = (1 + sqrt 5) / 4.
Proof. radcan_trig. Qed.

(* IMO 1963 (Tutorial 35) in one call *)
Lemma imo1963 : cos (PI / 7) - cos (2 * PI / 7) + cos (3 * PI / 7) = 1 / 2.
Proof. radcan_trig. Qed.

(* tan: the denominators give conditions, closed from the hypotheses;
   cos x * cos y - sin x * sin y <> 0 is closed as cos (x + y) <> 0 *)
Lemma tanD x y : cos x <> 0 -> cos y <> 0 -> cos (x + y) <> 0 ->
  tan (x + y) = (tan x + tan y) / (1 - tan x * tan y).
Proof. move=> hx hy hxy. radcan_trig. Qed.

(* without the hypotheses, the conditions are left, on R *)
Lemma tanD' x y : tan (x + y) = (tan x + tan y) / (1 - tan x * tan y).
Proof.
radcan_trig.
(* 4 goals: cos y <> 0, cos x <> 0, cos x * cos y - sin x * sin y <> 0,
   cos (x + y) <> 0 *)
Abort.

(* closed conditions are closed by the sign of cos on the angle *)
Lemma tan_PI6 : tan (PI / 6) = sqrt 3 / 3.
Proof. radcan_trig. Qed.

(* a condition that is a factor of a hypothesis:
   cos (3 x) = cos x * (cos x ^ 2 - 3 * sin x ^ 2) *)
Lemma tan3 x : cos x <> 0 -> cos (3 * x) <> 0 ->
  tan (3 * x) = (3 * tan x - tan x ^ 3) / (1 - 3 * tan x ^ 2).
Proof. move=> h h3. radcan_trig. Qed.

(* a false identity is refused *)
Lemma cos2_false x : cos (2 * x) = 2 * cos x - 1.
Proof. Fail radcan_trig. Abort.
