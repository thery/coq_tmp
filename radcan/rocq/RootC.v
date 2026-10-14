(* The posroot instance on an algebraically closed numeric field, from      *)
(* ssrnum's n.-root (principal n-th root, nonnegative on nonnegatives).      *)

From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section RootC.

Variable C : numClosedFieldType.

Lemma rootC_posroot_ge0 n (a : C) : (0 < n)%N -> 0 <= a -> 0 <= n.-root a.
Proof. by move=> n0 a0; rewrite rootC_ge0. Qed.

Lemma rootC_posrootK n (a : C) : (0 < n)%N -> 0 <= a -> n.-root a ^+ n = a.
Proof. by move=> n0 _; rewrite rootCK. Qed.

Lemma rootC_posrootM n (a b : C) : (0 < n)%N -> 0 <= a -> 0 <= b ->
  n.-root (a * b) = n.-root a * n.-root b.
Proof. by move=> _ a0 _; rewrite rootCMl. Qed.

Definition rootC_posroot : posroot C :=
  PosRoot rootC_posroot_ge0 rootC_posrootK rootC_posrootM.

Lemma rootC_posrootE n (a : C) : proot rootC_posroot n a = n.-root a.
Proof. by []. Qed.

(* Sanity check. *)
Lemma rootC_posroot_sqrt4 : proot rootC_posroot 2 4 = 2 :> C.
Proof. by apply: proot_eq; rewrite // ?ler0n // expr2 -natrM. Qed.

End RootC.

(* M9: roots of negative numbers through the principal roots of -1 *)
Section NegRootC.

Variable C : numClosedFieldType.

Lemma rootC_prootNw n (a : C) : (0 < n)%N -> 0 <= a ->
  n.-root (- a) = n.-root a * n.-root (-1).
Proof. by move=> _ a0; rewrite -rootCMl // mulrN1. Qed.

Lemma rootC_wrootK n : (0 < n)%N -> n.-root (-1 : C) ^+ n = -1.
Proof. by move=> n0; rewrite rootCK. Qed.

Definition rootC_negroot : negroot (rootC_posroot C) :=
  @NegRoot C (rootC_posroot C) (fun n => n.-root (-1)) rootC_prootNw rootC_wrootK.

End NegRootC.
