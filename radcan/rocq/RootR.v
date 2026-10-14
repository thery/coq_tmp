(******************************************************************************)
(* RootR: the root instances on a real closed field R.  mathcomp has no n-th  *)
(* root on rcfType: poly_ivt on 'X^n - a%:P over [0, 1 + a] gives a           *)
(* nonnegative root, picked with xchoose.                                     *)
(*   rootR0 n a == the nonnegative n-th root of a (0 unless 0 < n, 0 <= a)    *)
(*   rootR n a  == the real n-th root: rootR0 n a when 0 <= a,                *)
(*                 - rootR0 n (- a) when a < 0 and n odd, 0 otherwise         *)
(*                 (like Stdlib's sqrt)                                       *)
(*   rootR_posroot R : posroot R                                              *)
(*   rootR_oddroot R : oddroot (rootR_posroot R)                              *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section RootR.

Variable R : rcfType.

Implicit Types (a b x : R) (n : nat).

Lemma rootR_ex_pos n a : (0 < n)%N -> 0 <= a ->
  exists2 x, 0 <= x & x ^+ n = a.
Proof.
move=> n0 a0; have a1 : 0 <= 1 + a by rewrite addr_ge0.
have [|x /andP[x0 _] /rootP] := @poly_ivt R ('X^n - a%:P) 0 (1 + a) a1.
  rewrite !hornerE expr0n eqn0Ngt n0 sub0r oppr_le0 a0 /= subr_ge0.
  by rewrite (le_trans _ (ler_eXnr _ _)) // ?lerDr ?lerDl.
by rewrite !hornerE => /eqP; rewrite subr_eq0 => /eqP xa; exists x.
Qed.

(* outside 0 < n, 0 <= a the root is 0, like Stdlib's sqrt *)
Definition rootR_spec n a x :=
  (0 <= x) && (if (0 < n)%N && (0 <= a) then x ^+ n == a else x == 0).

Lemma rootR_ex n a : exists x, rootR_spec n a x.
Proof.
rewrite /rootR_spec.
case: (boolP ((0 < n)%N && (0 <= a))) => [/andP[n0 a0]|_].
  by have [x x0 xa] := rootR_ex_pos n0 a0; exists x; rewrite x0 xa eqxx.
by exists 0; rewrite lexx eqxx.
Qed.

Definition rootR0 n a : R := xchoose (rootR_ex n a).

Lemma rootR0_ge0 n a : 0 <= rootR0 n a.
Proof. by have /andP[] := xchooseP (rootR_ex n a). Qed.

Lemma rootR0K n a : (0 < n)%N -> 0 <= a -> rootR0 n a ^+ n = a.
Proof.
move=> n0 a0; have /andP[_] := xchooseP (rootR_ex n a).
by rewrite n0 a0 => /eqP.
Qed.

Lemma rootR0_out n a : ~~ ((0 < n)%N && (0 <= a)) -> rootR0 n a = 0.
Proof.
move=> /negbTE h; have /andP[_] := xchooseP (rootR_ex n a).
by rewrite h => /eqP.
Qed.

Definition rootR n a : R :=
  if 0 <= a then rootR0 n a else if odd n then - rootR0 n (- a) else 0.

Lemma rootR_ge0 n a : 0 <= a -> 0 <= rootR n a.
Proof. by rewrite /rootR => ->; apply: rootR0_ge0. Qed.

Lemma rootRK n a : (0 < n)%N -> 0 <= a -> rootR n a ^+ n = a.
Proof. by rewrite /rootR => n0 a0; rewrite a0 rootR0K. Qed.

Lemma rootR_out n a : ~~ ((0 < n)%N && (odd n || (0 <= a))) -> rootR n a = 0.
Proof.
rewrite /rootR; case: n => [|n] /=.
  by move=> _; case: ifP => // a0; rewrite rootR0_out.
by rewrite negb_or negbK => /andP[-> /negbTE ->].
Qed.

Lemma rootRN n a : odd n -> rootR n (- a) = - rootR n a.
Proof.
move=> On; rewrite /rootR On oppr_ge0 opprK.
have [a0|a0|->] := ltgtP a 0.
- by rewrite opprK.
- by [].
have n0 : (0 < n)%N by case: (n) On.
have : rootR0 n 0 ^+ n == 0 by rewrite rootR0K.
by rewrite expf_eq0 n0 /= oppr0 => /eqP ->; rewrite oppr0.
Qed.

Lemma rootRM n a b : (0 < n)%N -> 0 <= a -> 0 <= b ->
  rootR n (a * b) = rootR n a * rootR n b.
Proof.
move=> n0 a0 b0; apply/eqP.
rewrite -(eqrXn2 n0 (rootR_ge0 _ _)) ?mulr_ge0 ?rootR_ge0 //.
by rewrite exprMn !rootRK ?mulr_ge0.
Qed.

Definition rootR_posroot : posroot R :=
  PosRoot (fun n a (_ : (0 < n)%N) (a0 : 0 <= a) => rootR_ge0 n a0)
    rootRK rootRM.

Lemma rootR_posrootE n a : proot rootR_posroot n a = rootR n a.
Proof. by []. Qed.

Lemma rootR_oddroot : oddroot rootR_posroot.
Proof. by split=> n a On; apply: rootRN. Qed.

(* Sanity check. *)
Lemma rootR_posroot_sqrt4 : proot rootR_posroot 2 4 = 2 :> R.
Proof. by apply: proot_eq; rewrite // ?ler0n // expr2 -natrM. Qed.

End RootR.
