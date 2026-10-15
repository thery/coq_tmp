(******************************************************************************)
(* Tutorial 3: reified expressions rexpr and their value rinterp.             *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot Syntax.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Tutorial3.
Variables (F : numFieldType) (r : posroot F).
Local Notation "n .-proot" := (proot r n) (at level 2, format "n .-proot").
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).

Definition e1 : rexpr :=
  RMul (RRoot 2%positive 2%positive) (RRoot 2%positive 3%positive).

Lemma e1_val : rinterp r [::] e1 = \sqrt 2 * \sqrt 3.
Proof. by []. Qed.

Lemma e2_val :
  rinterp r [::] (RPow (RAdd (RCst (Zpos 1)) (RRoot 2%positive 2%positive)) 2) =
  (1 + \sqrt 2) ^+ 2.
Proof. by []. Qed.
End Tutorial3.
