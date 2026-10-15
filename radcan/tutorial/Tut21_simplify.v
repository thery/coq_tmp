From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot RootC RootR Syntax Radcan.
From Radcan Require Import RealRoot Refine Tactic Simplify SimplifyTac.
Import Order.TTheory GRing.Theory Num.Theory.

(* Part 21: radcan_simplify, the analogue of ring_simplify (milestone M17). *)
(* Each side of the goal is replaced by its normal form, printed back as a *)
(* mathcomp expression; the side conditions come after the main goal.     *)

Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(* simplifying the goal again leaves it unchanged *)
Ltac check_stable :=
  lazymatch goal with
  | |- ?g =>
      radcan_simplify;
      [lazymatch goal with
       | |- g => idtac
       | |- ?h => fail 0 "radcan_simplify is not stable:" g h
       end|..]
  end.

Section Simplify.
Variables (F : numFieldType) (r : posroot F) (x y : F).
Local Notation "n .-proot" := (proot r n) (at level 2, format "n .-proot").
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).

Lemma s1 : \sqrt 12 - \sqrt 3 = y.
Proof.
radcan_simplify.
Show. (* \sqrt 3 = y *)
check_stable.
Abort.

Lemma s2 : 1 / (1 + \sqrt 2) = y.
Proof.
radcan_simplify.
Show. (* \sqrt 2 - 1 = y *)
check_stable.
Abort.

Lemma s3 : (1 + \sqrt 2) ^+ 2 = y.
Proof.
radcan_simplify.
Show. (* 2 * \sqrt 2 + 3 = y *)
check_stable.
Abort.

Lemma s4 : \sqrt (x ^+ 2 + 2 * x + 1) = y.
Proof.
radcan_simplify.
Show. (* x + 1 = y,  side condition -1 <= x *)
check_stable.
Abort.

Lemma s5 : (x - y) / (\sqrt x + \sqrt y) = 0.
Proof.
radcan_simplify.
Show. (* \sqrt x - \sqrt y = 0,  0 <= x, 0 <= y, x != y *)
check_stable.
Abort.

(* the raw conditions, before refinement *)
Lemma s5_raw : (x - y) / (\sqrt x + \sqrt y) = 0.
Proof.
radcan_simplify_raw.
Show. (* \sqrt x - \sqrt y = 0,  0 <= x, 0 <= y, -1 * y + x != 0 *)
Abort.

Lemma s6 : \sqrt x * 3.-proot x = y.
Proof.
radcan_simplify.
Show. (* 6.-proot (x ^+ 5) = y,  0 <= x *)
check_stable.
Abort.

(* a common denominator *)
Lemma s7 : (\sqrt x + \sqrt y) / (\sqrt x - \sqrt y) = 0.
Proof.
radcan_simplify.
Show. (* (x + y + 2 * \sqrt x * \sqrt y) / (x - y) = 0 *)
check_stable.
Abort.

(* polynomials: higher powers of the first variable first *)
Lemma s8 : (x - 2 * y + 1) ^+ 3 = 0.
Proof.
radcan_simplify.
Show.
(* x ^+ 3 - 6 * x ^+ 2 * y + 3 * x ^+ 2 + 12 * x * y ^+ 2 - 12 * x * y
   + 3 * x - 8 * y ^+ 3 + 12 * y ^+ 2 - 6 * y + 1 = 0 *)
check_stable.
Abort.

(* other relations, and a hypothesis *)
Lemma s9 : \sqrt 12 + x <= \sqrt 27.
Proof.
radcan_simplify.
Show. (* x + 2 * \sqrt 3 <= 3 * \sqrt 3 *)
Abort.

Lemma s10 : y = \sqrt 8 * \sqrt 2 -> y ^+ 2 = 16.
Proof.
move=> H.
radcan_simplify in H.
Show. (* H : y = 4 *)
by rewrite H -natrX.
Qed.

(* only one subterm, rewritten everywhere in the goal *)
Lemma s11 : x * (\sqrt 12 + x) = \sqrt 12 + x.
Proof.
radcan_simplify_term (\sqrt 12 + x).
Show. (* x * (x + 2 * \sqrt 3) = x + 2 * \sqrt 3 *)
Abort.

End Simplify.

(* root-free goals: no root structure is needed *)
Section RootFree.
Variables (F : numFieldType) (x y : F).

Lemma f1 : (x ^+ 2 - y ^+ 2) / (x - y) - x * 3 / 6 = 0.
Proof.
radcan_simplify.
Show. (* x / 2 + y = 0,  x != y *)
check_stable.
Abort.

End RootFree.

(* C: n.-root, negative radicands through roots of -1 *)
Section C.
Variables (C : numClosedFieldType) (z : C).

Lemma c1 : 2.-root (-4 : C) + 3.-root 16 - 3.-root 2 = z.
Proof.
radcan_simplify.
Show. (* 2 * sqrtC (-1) + 3.-root 2 = z *)
check_stable.
Abort.

Lemma c2 : 2.-root z * 3.-root z = 0.
Proof.
radcan_simplify.
Show. (* 6.-root (z ^+ 5) = 0,  0 <= z *)
check_stable.
Abort.

End C.

(* real closed fields: rootR, odd roots of negative numbers *)
Section R.
Variables (R : rcfType) (x : R).

Lemma r1 : rootR 3 (-8 : R) + rootR 2 (x ^+ 2 * 8) - rootR 3 (x ^+ 3) = 0.
Proof.
radcan_simplify.
Show. (* 2 * `|x| * rootR 2 2 - x - 2 = 0, no condition (real mode) *)
check_stable.
Abort.

End R.

(* real mode: on an rcfType (rootR) or with a realroot r in the context,  *)
(* `|a| is read as rootR 2 (a ^+ 2) and printed back as `|a|; even roots  *)
(* of even powers and odd roots of any sign need no condition             *)
Section RealMode.
Variables (R : rcfType) (x y : R).

Lemma a1 : rootR 2 ((x - 2) ^+ 2) = y.
Proof.
radcan_simplify.
Show. (* `|x - 2| = y,  no condition *)
check_stable.
Abort.

Lemma a2 : rootR 2 (x ^+ 2 * y ^+ 2) = 0.
Proof.
radcan_simplify.
Show. (* `|x| * `|y| = 0,  no condition *)
check_stable.
Abort.

Lemma a3 : rootR 3 (- 8 * x ^+ 3) = y.
Proof.
radcan_simplify.
Show. (* - (2 * x) = y,  no condition *)
check_stable.
Abort.

Lemma a4 : rootR 3 (x ^+ 2) * rootR 3 x = y.
Proof.
radcan_simplify.
Show. (* x = y,  no condition *)
check_stable.
Abort.

Lemma a5 : rootR 2 (4 * x ^+ 2) + `|x| = y.
Proof.
radcan_simplify.
Show. (* 3 * `|x| = y,  no condition *)
check_stable.
Abort.

Lemma a6 : `|x| ^+ 2 = y.
Proof.
radcan_simplify.
Show. (* x ^+ 2 = y,  no condition *)
check_stable.
Abort.

End RealMode.

(* any posroot on a realFieldType with an oddroot gives a realroot *)
Section RealField.
Variables (F : realFieldType) (r : posroot F) (o : oddroot r) (x y : F).
Local Notation "n .-proot" := (proot r n) (at level 2, format "n .-proot").
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).
Let rl := realroot_of o.

Lemma g1 : \sqrt ((x + 1) ^+ 2) - 3.-proot (- x ^+ 3) = y.
Proof.
radcan_simplify.
Show. (* x + `|x + 1| = y,  no condition *)
check_stable.
Abort.

Lemma g2 : `|x| * \sqrt (4 * x ^+ 2) = y.
Proof.
radcan_simplify.
Show. (* 2 * x ^+ 2 = y *)
check_stable.
Abort.

End RealField.
