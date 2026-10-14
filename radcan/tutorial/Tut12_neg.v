From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts RootC RootR Syntax Radcan Refine Tactic OddRoot.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* with an oddroot o : oddroot r in the context, radcan uses the odd mode;  *)
(* on rootR it always does (rootR_oddroot)                                   *)

Section Odd.
Variables (F : numFieldType) (r : posroot F) (o : oddroot r) (x : F).

Lemma n1 : proot r 3 (- 8) = - 2.
Proof. by radcan. Qed.

Lemma n2 : proot r 3 (- 2) * proot r 3 (- 4) = 2.
Proof. by radcan. Qed.

Lemma n3 : proot r 3 (- 3) ^+ 3 = - 3.
Proof. by radcan. Qed.

Lemma n4 : proot r 5 (- 32) + 2 = 0.
Proof. by radcan. Qed.

(* the cube root of 1 - x is minus the cube root of x - 1, no condition *)
Lemma n5 : proot r 3 (1 - x) = - proot r 3 (x - 1).
Proof. by radcan. Qed.

(* raw: 0 <= x - 1   refined: 1 <= x *)
Lemma n6 : 1 <= x -> proot r 3 (1 - x) * proot r 3 (x - 1) ^+ 2 = 1 - x.
Proof. move=> x_ge1. radcan. Show. exact: x_ge1. Qed.
End Odd.

Section Even.
Variables (F : numFieldType) (r : posroot F) (x : F).

(* without an oddroot the cube root of -8 is not simplified *)
Goal proot r 3 (- 8) = - 2.
Proof. Fail radcan. Abort.

(* even roots: the base keeps the sign of the radicand  *)
(* raw: 0 <= 1 - x (printed -1 * x + 1)   refined: x <= 1 *)
Lemma e1 : x <= 1 -> proot r 2 (1 - x) ^+ 2 = 1 - x.
Proof. move=> x_le1. radcan. Show. exact: x_le1. Qed.

(* x - 1 is in the basis: sqrt (1 - x) still has base 1 - x *)
(* raw: 0 <= x - 1, 0 <= 1 - x   refined: 1 <= x, x <= 1 *)
Lemma e2 : x = 1 -> proot r 2 (x - 1) ^+ 2 + proot r 2 (1 - x) ^+ 2 = 0.
Proof. move=> x1. radcan. Show. all: by rewrite x1. Qed.

(* sqrt (1 - x) * sqrt (x - 1) = 0 needs x = 1: not found *)
Goal proot r 2 (1 - x) * proot r 2 (x - 1) = 0.
Proof. Fail radcan. Abort.
End Even.

(* on a real closed field, with rootR and its oddroot *)
Lemma rn1 (R : rcfType) : rootR 3 (- 8) = - 2 :> R.
Proof. by radcan. Qed.

Lemma rn2 (R : rcfType) (x : R) : rootR 3 (1 - x) + rootR 3 (x - 1) = 0.
Proof. by radcan. Qed.

(* on C, the principal cube root of -8 is not -2: radcan refuses *)
Goal forall C : numClosedFieldType, 3.-root (-8 : C) = -2.
Proof. move=> C. Fail radcan. Abort.
