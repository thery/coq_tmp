(******************************************************************************)
(* PosRootFacts: derived facts on a posroot, oddroot or negroot instance.     *)
(*                                                                            *)
(* All lemmas follow from the uniqueness of nonnegative n-th roots (proot_eq, *)
(* from eqrXn2) and the record fields.                                        *)
(*   proot_eq     : 0 <= x -> x ^+ n = a -> proot r n a = x                   *)
(*   prootX, proot_proot, prootV, prootM_big, ... : the usual root laws       *)
(*   prootNK      : odd roots of reals, given an oddroot                      *)
(*   oddroot_ge0  : on a realFieldType, the odd law for 0 <= a gives oddroot  *)
(*   wrootE       : wroot w n = proot r n (-1), given w : negroot r           *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section PosRootFacts.

Variables (F : numFieldType) (r : posroot F).

Implicit Types (a b x : F) (n m k : nat).

(* Uniqueness: a nonnegative x with x ^+ n = a is the n-th root of a. *)
Lemma proot_eq n a x : (0 < n)%N -> 0 <= x -> x ^+ n = a -> proot r n a = x.
Proof.
move=> n0 x0 xa; have a0 : 0 <= a by rewrite -xa exprn_ge0.
by apply/eqP; rewrite -(eqrXn2 n0 (proot_ge0 r n0 a0) x0) prootK // xa.
Qed.

Lemma prootXK n a : (0 < n)%N -> 0 <= a -> proot r n (a ^+ n) = a.
Proof. by move=> n0 a0; apply: proot_eq. Qed.

Lemma prootX n m a : (0 < n)%N -> 0 <= a ->
  proot r n (a ^+ m) = proot r n a ^+ m.
Proof.
move=> n0 a0; apply: proot_eq => //; first by rewrite exprn_ge0 // proot_ge0.
by rewrite -exprM mulnC exprM prootK.
Qed.

Lemma prootMn n k a : (0 < n)%N -> (0 < k)%N -> 0 <= a ->
  proot r (n * k) a ^+ k = proot r n a.
Proof.
move=> n0 k0 a0; have nk0 : (0 < n * k)%N by rewrite muln_gt0 n0.
apply/esym/proot_eq => //; first by rewrite exprn_ge0 // proot_ge0.
by rewrite -exprM [(k * n)%N]mulnC prootK.
Qed.

Lemma proot_mulr n k a : (0 < n)%N -> (0 < k)%N -> 0 <= a ->
  proot r n a = proot r (n * k) (a ^+ k).
Proof.
move=> n0 k0 a0; have nk0 : (0 < n * k)%N by rewrite muln_gt0 n0.
by apply/esym/proot_eq; rewrite ?proot_ge0 // exprM prootK.
Qed.

Lemma proot_proot n k a : (0 < n)%N -> (0 < k)%N -> 0 <= a ->
  proot r n (proot r k a) = proot r (n * k) a.
Proof.
move=> n0 k0 a0; have nk0 : (0 < n * k)%N by rewrite muln_gt0 n0.
by apply: proot_eq; rewrite ?proot_ge0 // mulnC prootMn.
Qed.

Lemma proot1n a : 0 <= a -> proot r 1 a = a.
Proof. by move=> a0; apply: proot_eq; rewrite ?expr1. Qed.

Lemma proot_1 n : (0 < n)%N -> proot r n 1 = 1.
Proof. by move=> n0; apply: proot_eq; rewrite ?expr1n. Qed.

Lemma proot_0 n : (0 < n)%N -> proot r n 0 = 0.
Proof. by move=> n0; apply: proot_eq; rewrite // expr0n eqn0Ngt n0. Qed.

Lemma proot_eq0 n a : (0 < n)%N -> 0 <= a -> (proot r n a == 0) = (a == 0).
Proof.
move=> n0 a0; apply/eqP/eqP => [p0|->]; last exact: proot_0.
by rewrite -(prootK r n0 a0) p0 expr0n eqn0Ngt n0.
Qed.

Lemma proot_gt0 n a : (0 < n)%N -> 0 < a -> 0 < proot r n a.
Proof.
move=> n0 a0; have a0' := ltW a0.
by rewrite lt_def proot_eq0 // (gt_eqF a0) proot_ge0.
Qed.

Lemma proot_inj n a b : (0 < n)%N -> 0 <= a -> 0 <= b ->
  proot r n a = proot r n b -> a = b.
Proof. by move=> n0 a0 b0 eab; rewrite -(prootK r n0 a0) eab prootK. Qed.

Lemma prootV n a : (0 < n)%N -> 0 <= a ->
  proot r n a^-1 = (proot r n a)^-1.
Proof.
move=> n0 a0; apply: proot_eq; rewrite ?invr_ge0 ?proot_ge0 //.
by rewrite exprVn prootK.
Qed.

Lemma prootM_big (I : Type) n (s : seq I) (P : pred I) (f : I -> F) :
  (0 < n)%N -> (forall i, P i -> 0 <= f i) ->
  proot r n (\prod_(i <- s | P i) f i) = \prod_(i <- s | P i) proot r n (f i).
Proof.
move=> n0 f0; elim: s => [|i s IH]; first by rewrite !big_nil proot_1.
rewrite !big_cons; case: ifP => // Pi.
by rewrite prootM ?f0 ?IH // prodr_ge0.
Qed.

End PosRootFacts.

Section OddRootFacts.

Variables (F : numFieldType) (r : posroot F) (o : oddroot r).

Implicit Types (a b : F) (n : nat).

Lemma prootNK n a : odd n -> a \is Num.real -> proot r n a ^+ n = a.
Proof.
move=> On ar; have n0 : (0 < n)%N by case: n On.
have [a0|a0] := real_ge0P ar; first exact: prootK.
rewrite -(opprK a) (prootN o) // exprNn -signr_odd On expr1 mulN1r.
by rewrite prootK // oppr_ge0 ltW.
Qed.

End OddRootFacts.

Lemma oddroot_ge0 (F : realFieldType) (r : posroot F) :
  (forall n a, odd n -> 0 <= a -> proot r n (- a) = - proot r n a) ->
  oddroot r.
Proof.
move=> H; split=> n a On; have [a0|a0] := leP 0 a; first exact: H.
have := H n (- a) On; rewrite opprK oppr_ge0 => /(_ (ltW a0)) ->.
by rewrite opprK.
Qed.

Section NegRootFacts.

Variables (F : numFieldType) (r : posroot F) (w : negroot r).

Implicit Types (a : F) (n : nat).

Lemma wrootE n : (0 < n)%N -> wroot w n = proot r n (-1).
Proof. by move=> n0; rewrite (prootNw w n0 ler01) proot_1 // mul1r. Qed.

Lemma prootN1K n : (0 < n)%N -> proot r n (-1) ^+ n = -1.
Proof. by move=> n0; rewrite -wrootE // wrootK. Qed.

Lemma prootN1 n a : (0 < n)%N -> 0 <= a ->
  proot r n (- a) = proot r n a * proot r n (-1).
Proof. by move=> n0 a0; rewrite (prootNw w n0 a0) wrootE. Qed.

End NegRootFacts.
