(******************************************************************************)
(* Tutorial 20 (M13): nested radicands, absolute values and odd roots of any  *)
(* sign on real fields.                                                       *)
(*   nested: a radicand containing roots is normalised first; if its normal   *)
(*      form is root-free, its factors join the basis (any posroot)           *)
(*   real fields (realroot r, RealRoot.v; rootR_realroot on an rcfType):      *)
(*      |a| = proot r 2 (a ^+ 2); even roots of even powers give |B| with no  *)
(*      condition; odd roots split and reduce with no sign condition          *)
(*   tactic: radcan picks the real mode on rootR goals and with a            *)
(*      realroot r in the context (checker radcan_check_real, AbsRoot.v)     *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts RootC RootR RealRoot Syntax.
From Radcan Require Import Radcan Refine Tactic NegRootC AbsRoot.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Section Nested.
Variables (F : numFieldType) (r : posroot F) (x : F).
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).

(* the paper's nested example (section 2):                                  *)
(* raw: 0 <= x + 1, 0 <= x + 2   refined: -1 <= x                           *)
Lemma nest1 : -1 <= x ->
  \sqrt (x ^+ 2 + 3 * x + 3 + \sqrt (x + 1) * \sqrt (x + 1)) = x + 2.
Proof. move=> h. Time radcan. Show. exact: h. Qed.

(* the inner radicand is a square too *)
Lemma nest2 : 0 <= x ->
  \sqrt (\sqrt (x ^+ 2) * \sqrt (x ^+ 2)) = x.
Proof. move=> h. Time radcan. exact: h. Qed.
End Nested.

Section Real.
Variables (R : rcfType) (x y : R).

(* no condition: even roots of even powers are absolute values *)
Lemma a1 : rootR 2 ((x - 2) ^+ 2) = `|x - 2|.
Proof. Time by radcan. Qed.

Lemma a2 : rootR 2 (x ^+ 2) = `|x|.
Proof. by radcan. Qed.

Lemma a3 : rootR 2 (x ^+ 2 * y ^+ 2) = `|x| * `|y|.
Proof. by radcan. Qed.

Lemma a4 : rootR 2 (x ^+ 2) ^+ 2 = x ^+ 2.
Proof. by radcan. Qed.

(* the radicand x^2 - 4x + 4 is seen as (x - 2)^2 *)
Lemma a5 : rootR 2 (x ^+ 2 - 4 * x + 4) = `|x - 2|.
Proof. by radcan. Qed.

Lemma a6 : rootR 2 (4 * x ^+ 2) = 2 * `|x|.
Proof. by radcan. Qed.

Lemma a7 : `|x| ^+ 2 = x ^+ 2.
Proof. by radcan. Qed.

Lemma a8 : rootR 4 (x ^+ 4) = `|x|.
Proof. by radcan. Qed.

(* |B| is not B: with |x|, sqrt (x^2) = x is refused, then retried with  *)
(* x and the condition 0 <= x (refined: 0 <= x)                          *)
Lemma a9 : 0 <= x -> rootR 2 (x ^+ 2) = x.
Proof. move=> h. radcan. Show. exact: h. Qed.

(* odd roots of any sign: no condition *)
Lemma o1 : rootR 3 (x ^+ 3) = x.
Proof. Time by radcan. Qed.

Lemma o2 : rootR 3 (- 8 * x ^+ 3) = - 2 * x.
Proof. by radcan. Qed.

Lemma o3 : rootR 3 (x * y) = rootR 3 x * rootR 3 y.
Proof. by radcan. Qed.

Lemma o4 : rootR 3 (x ^+ 2) * rootR 3 x = x.
Proof. by radcan. Qed.

Lemma o5 : rootR 3 x * rootR 5 x = rootR 15 (x ^+ 8).
Proof. by radcan. Qed.

(* the odd mode (oddroot only) still asks 0 <= x *)
Lemma o6 : 0 <= x -> rootR 3 (x ^+ 3) = x.
Proof.
move=> h. radcan_with_gen true (rootR_posroot R) (rootR_oddroot R). exact: h.
Qed.
End Real.

(* any posroot on a realFieldType with an oddroot gives a realroot *)
Section RealField.
Variables (F : realFieldType) (r : posroot F) (o : oddroot r) (x : F).
Let rl := realroot_of o.

Lemma f1 : proot r 2 ((x + 1) ^+ 2) = `|x + 1|.
Proof. by radcan. Qed.

Lemma f2 : proot r 3 (- x ^+ 3) = - x.
Proof. by radcan. Qed.
End RealField.

(* the paper's (4) = (6) on C, with omega = 3.-root (-1) (the paper prints *)
(* omega_6 for (-1)^(1/3) = omega_6 ^+ 2 in its convention); raw and      *)
(* conditions: raw 0 <= x ^+ 2 + 1, refined -1 <= x ^+ 2                   *)
Section Paper46.
Variables (C : numClosedFieldType) (x : C).

Lemma eq46 : -1 <= x ^+ 2 ->
  (4.-root 2 + 2.-root 3 * 3.-root (- (x ^+ 2 + 1))) / 2.-root (x ^+ 2 + 1) =
  1 / (x ^+ 2 + 1) * 4.-root 2 * 6.-root (x ^+ 2 + 1) ^+ 3 +
  1 / (x ^+ 2 + 1) * 3.-root (-1) * 2.-root 3 * 6.-root (x ^+ 2 + 1) ^+ 5.
Proof. move=> h. Time radcan. Show. exact: h. Qed.

(* with a 6th root of -1 it is false (at x = 0 it says                     *)
(* 3.-root (-1) = 6.-root (-1), but their 6th powers are 1 and -1)         *)
Goal (4.-root 2 + 2.-root 3 * 3.-root (- (x ^+ 2 + 1))) / 2.-root (x ^+ 2 + 1) =
  1 / (x ^+ 2 + 1) * 4.-root 2 * 6.-root (x ^+ 2 + 1) ^+ 3 +
  1 / (x ^+ 2 + 1) * 6.-root (-1) * 2.-root 3 * 6.-root (x ^+ 2 + 1) ^+ 5.
Proof. Fail radcan. Abort.
End Paper46.
