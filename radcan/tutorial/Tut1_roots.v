From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts RootC RootR.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Tutorial1.
Variables (F : numFieldType) (r : posroot F).

Lemma sqrt2_sq : proot r 2 2 ^+ 2 = 2.
Proof. by rewrite prootK. Qed.

Lemma sqrt2_ge0 : 0 <= proot r 2 2.
Proof. by apply: proot_ge0. Qed.

Lemma sqrt2_sqrt3 : proot r 2 2 * proot r 2 3 = proot r 2 6.
Proof. by rewrite -prootM // -natrM. Qed.

Lemma sqrt4 : proot r 2 4 = 2.
Proof. by apply: proot_eq => //; rewrite expr2 -natrM. Qed.

Lemma cbrt_sqrt : proot r 3 2 = proot r 6 4.
Proof. by rewrite (proot_mulr r (k := 2)) // expr2 -natrM. Qed.
End Tutorial1.

Section Tutorial2.
Variables (R : rcfType) (C : numClosedFieldType).
Lemma sqrt2_sqrt3_R : proot (rootR_posroot R) 2 2 * proot (rootR_posroot R) 2 3 = proot (rootR_posroot R) 2 6 :> R.
Proof. exact: sqrt2_sqrt3. Qed.
Lemma sqrt2_sqrt3_C : 2.-root 2 * 2.-root 3 = 2.-root 6 :> C.
Proof. by rewrite -!rootC_posrootE sqrt2_sqrt3. Qed.
End Tutorial2.
