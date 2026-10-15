(******************************************************************************)
(* Tutorial 1: the root interface posroot (PosRoot.v) and its laws            *)
(* (PosRootFacts.v), on any numFieldType, rcfType (rootR) and C (n.-root).    *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts RootC RootR.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Tutorial1.
Variables (F : numFieldType) (r : posroot F).
Local Notation "n .-proot" := (proot r n) (at level 2, format "n .-proot").
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).

Lemma sqrt2_sq : \sqrt 2 ^+ 2 = 2.
Proof. by rewrite prootK. Qed.

Lemma sqrt2_ge0 : 0 <= \sqrt 2.
Proof. by apply: proot_ge0. Qed.

Lemma sqrt2_sqrt3 : \sqrt 2 * \sqrt 3 = \sqrt 6.
Proof. by rewrite -prootM // -natrM. Qed.

Lemma sqrt4 : \sqrt 4 = 2.
Proof. by apply: proot_eq => //; rewrite expr2 -natrM. Qed.

Lemma cbrt_sqrt : 3.-proot 2 = 6.-proot 4.
Proof. by rewrite (proot_mulr r (k := 2)) // expr2 -natrM. Qed.
End Tutorial1.

Section Tutorial2.
Variables (R : rcfType) (C : numClosedFieldType).
Lemma sqrt2_sqrt3_R :
  proot (rootR_posroot R) 2 2 * proot (rootR_posroot R) 2 3 =
  proot (rootR_posroot R) 2 6 :> R.
Proof. exact: sqrt2_sqrt3. Qed.
Lemma sqrt2_sqrt3_C : 2.-root 2 * 2.-root 3 = 2.-root 6 :> C.
Proof. by rewrite -!rootC_posrootE sqrt2_sqrt3. Qed.

End Tutorial2.
