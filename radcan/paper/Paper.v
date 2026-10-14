(* The examples of Caviness & Fateman, "Simplification of Radical            *)
(* Expressions" (radcan.md), run through radcan.                             *)
(* Proved: §2 phase 3 and form 2 examples, (1) as an identity, (8), and the   *)
(* rationalisation of D at the end of §2.                                     *)
(* Refused because FALSE: (3) as printed, and E with the printed 54 x (the     *)
(* right coefficient is 108 x).                                               *)
(* Not proved (out of scope): quotients whose denominator mixes variables and *)
(* roots ((1), (3) as quotients), (2) and (4)=(6) on C, the nested example.   *)

From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts RootC RootR Syntax Radcan Refine Tactic OddRoot NegRootC.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Paper.
Variables (F : numFieldType) (r : posroot F) (x y : F).
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).

(* (1): x - y over sqrt x + sqrt y is sqrt x - sqrt y *)
Lemma eq1 : 0 <= x -> 0 <= y -> x - y = (\sqrt x - \sqrt y) * (\sqrt x + \sqrt y).
Proof. move=> hx hy. radcan. all: by []. Qed.
(* as a quotient it is not found: the denominator mixes variables and roots *)
Goal (x - y) / (\sqrt x + \sqrt y) = \sqrt x - \sqrt y.
Proof. Fail radcan. Abort.

(* §2, phase 3: (2^(1/6))^7 = 2 * 2^(1/6) *)
Lemma phase3 : proot r 6 2 ^+ 7 = 2 * proot r 6 2.
Proof. radcan. Qed.

(* §2, form 2: square-free factorisation of the radicand *)
Lemma form2 : -3 <= x -> -2 <= 3 * x + x ^+ 2 ->
  \sqrt (x ^+ 4 + 9 * x ^+ 3 + 29 * x ^+ 2 + 39 * x + 18) =
  (x + 3) * \sqrt (x ^+ 2 + 3 * x + 2).
Proof. move=> h1 h2. radcan. all: by []. Qed.

(* §2: with (x+2)^(1/3) the basis splits x^2 + 3x + 2 = (x+1)(x+2) and     *)
(* (x+2)^(1/2), (x+2)^(1/3) are merged over index 6                        *)
Lemma form1 : -1 <= x ->
  \sqrt (x ^+ 4 + 9 * x ^+ 3 + 29 * x ^+ 2 + 39 * x + 18) + proot r 3 (x + 2)
  = (x + 3) * \sqrt (x + 1) * proot r 6 ((x + 2) ^+ 3) + proot r 6 ((x + 2) ^+ 2).
Proof. move=> h. radcan. exact: h. Qed.

(* the nested example of §2 is out of scope *)
Goal \sqrt (x ^+ 2 + 3 * x + 3 + \sqrt (x + 1) * \sqrt (x + 1)) = x + 2.
Proof. Fail radcan. Abort.

(* (3) as printed is FALSE (check at x = 5/2): radcan refuses it *)
Goal (x + \sqrt 2 + proot r 3 9) *
  ((((2 * x ^+ 3 - 4 * x - 9) * \sqrt 2 - x ^+ 4 - 9 * x + 4) * proot r 3 9)
  + (((-9) * x ^+ 2 - 6) * \sqrt 2 + 3 * x ^+ 3 + 18 * x + 27) * proot r 3 3
  + ((- x ^+ 4 + 4 * x ^+ 2 + 18 * x - 4) * \sqrt 2 + x ^+ 5 - 4 * x ^+ 3 + 9 * x ^+ 2 + 4 * x + 18))
  = x ^+ 5 - 6 * x ^+ 4 + 18 * x ^+ 3 + 12 * x ^+ 2 + 108 * x + 73.
Proof. Fail radcan. Abort.

(* (8): 1 / (x + sqrt 2 + 3^(2/3)) = N / D with D = (x + sqrt 2)^3 + 9 *)
Lemma eq8 : (x + \sqrt 2 + proot r 3 9) *
  (- (x + \sqrt 2) * proot r 3 9 + 3 * proot r 3 3 + (x ^+ 2 + 2 * \sqrt 2 * x + 2))
  = (x + \sqrt 2) ^+ 3 + 9.
Proof. radcan. Qed.

(* end of §2: D times its conjugate is E; the paper prints 54 x, which is    *)
(* refused, the right coefficient is 108 x                                  *)
Goal ((x + \sqrt 2) ^+ 3 + 9) * (x ^+ 3 + 6 * x + 9 - (3 * x ^+ 2 + 2) * \sqrt 2)
   = x ^+ 6 - 6 * x ^+ 4 + 18 * x ^+ 3 + 12 * x ^+ 2 + 54 * x + 73.
Proof. Fail radcan. Abort.
Lemma eqE : ((x + \sqrt 2) ^+ 3 + 9) * (x ^+ 3 + 6 * x + 9 - (3 * x ^+ 2 + 2) * \sqrt 2)
   = x ^+ 6 - 6 * x ^+ 4 + 18 * x ^+ 3 + 12 * x ^+ 2 + 108 * x + 73.
Proof. radcan. Qed.
End Paper.

Section PaperC.
Variables (C : numClosedFieldType) (x : C).
(* (2): with mathcomp's principal roots the left side is - sqrt 2, not 0;    *)
(* the paper's convention (1-x)^(3/4) = ((1-x)^(1/4))^3 gives 0 but needs the *)
(* cyclotomic relation of omega_8, which radcan does not use                 *)
Goal 4.-root (x - 1) / 4.-root (1 - x) - 4.-root ((x - 1) ^+ 3) / 4.-root ((1 - x) ^+ 3)
     - 2.-root 2 = 0.
Proof. Fail radcan. Abort.
Goal 4.-root (x - 1) / 4.-root (1 - x) - 4.-root (x - 1) ^+ 3 / 4.-root (1 - x) ^+ 3
     - 2.-root 2 = 0.
Proof. Fail radcan. Abort.
End PaperC.
