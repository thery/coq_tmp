(******************************************************************************)
(* Tutorial 32 (M21): rationalised inverses with symbols.                     *)
(* With roots given by hypotheses (Tut30, radcan_sym), the paper (§2) works   *)
(* in the field Q(x)[y] / (y ^+ n - B): an inverse 1 / d, d mixing symbols,   *)
(* is rewritten u / E with d * u = E and E free of symbols.  As in M11        *)
(* (Ratio.v, Tut18) u and E come from a fraction-free elimination on the      *)
(* basis of the symbol monomials y ^+ k (k < n), the multiplication being     *)
(* reduced by the relations.  Only the product is trusted: E is computed as   *)
(* the reduced d * u and must be free of symbols; then                        *)
(*     inv_from_mul : d * u = E -> E != 0 -> d^-1 = u * E^-1                  *)
(* gives the new condition E != 0 (dropped when E is a nonzero constant).     *)
(* It is a fallback: radcan_check_sym first tries the plain normal forms, so  *)
(* the goals of Tut30 keep their conditions.  Same theorem:                   *)
(*   radcan_eq_cond_sym : radcan_check_sym rels e1 e2 = Some cs -> ...        *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot Syntax Radcan Tactic Sym SymTac.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* y = (x - 1)^(1/2): (1 + y) (y - 1) = y^2 - 1 = x - 2 *)
Section Sqrt.
Variables (F : numFieldType) (x y : F).
Hypothesis hy : y ^+ 2 = x - 1.

(* condition: x - 2 != 0 *)
Lemma syminv1 : x != 2 -> 1 / (1 + y) = (y - 1) / (x - 2).
Proof. move=> h. radcan_sym. by rewrite subr_eq0. Qed.

Lemma syminv2 : x != 2 -> 1 / (y + 1) + 1 / (y - 1) = 2 * y / (x - 2).
Proof. move=> h. radcan_sym. by rewrite subr_eq0. Qed.

Lemma syminv3 : x != 2 -> (x - 1) / (1 + y) = (x - 1) * (y - 1) / (x - 2).
Proof. move=> h. radcan_sym. by rewrite subr_eq0. Qed.

(* the plain check is tried first: no rationalisation, no x != 2 *)
Lemma syminv4 : y + 1 != 0 -> (1 + y) / (1 + y) = 1.
Proof. move=> h. radcan_sym. exact: h. Qed.
End Sqrt.

(* s = (x + 1)^(1/3): (1 + s) (1 - s + s^2) = 1 + s^3 = x + 2 *)
Section Cbrt.
Variables (F : numFieldType) (x s : F).
Hypothesis hs : s ^+ 3 = x + 1.

Lemma syminv5 : x != -2 -> 1 / (1 + s) = (1 - s + s ^+ 2) / (x + 2).
Proof. move=> h. radcan_sym. by rewrite addr_eq0. Qed.
End Cbrt.

(* two symbols: (y + z) (z - y) = z^2 - y^2 = 1, no condition at all *)
Section Two.
Variables (F : numFieldType) (x y z : F).
Hypotheses (hy : y ^+ 2 = x) (hz : z ^+ 2 = x + 1).

Lemma syminv6 : 1 / (y + z) = z - y.
Proof. radcan_sym. Qed.
End Two.

(* the paper's style: x + y + w, w = (-1)^(1/4), y = (x - 1)^(1/2); the     *)
(* basis has 8 monomials and E (the norm of x + y + w over Q(x)) degree 8;  *)
(* about 2.5 s for the tactic and 1 s for Qed                               *)
Section Stress.
Variables (F : numFieldType) (x y w : F).
Hypotheses (hy : y ^+ 2 = x - 1) (hw : w ^+ 4 = -1).

Lemma syminv7 : x ^+ 4 + 1 != 0 -> 1 / (x + w) =
  (x ^+ 3 - x ^+ 2 * w + x * w ^+ 2 - w ^+ 3) / (x ^+ 4 + 1).
Proof. move=> h. radcan_sym. exact: h. Qed.

Lemma syminv8 : x != 2 ->
  x ^+ 8 - 4 * x ^+ 7 + 10 * x ^+ 6 - 16 * x ^+ 5 + 21 * x ^+ 4
    - 4 * x ^+ 3 - 8 * x + 4 != 0 ->
  (x + y + w) * (1 / (x + y + w) + 1 / (1 + y)) =
  1 + (x + y + w) * (y - 1) / (x - 2).
Proof.
move=> h2 h. radcan_sym; first by rewrite subr_eq0.
(* E != 0, E printed in the normaliser's order *)
by move: h; apply: contra_neq => <-; radcan_sym.
Qed.
End Stress.
