(******************************************************************************)
(* RealRoot: roots on a field whose elements are all real (an rcfType).       *)
(*                                                                            *)
(*   realroot r   == record: r has an oddroot, and every element is real      *)
(*                   (realroot_of on a realFieldType, rootR_realroot on R)    *)
(* With rl : realroot r, for every a b (no sign condition):                   *)
(*   proot_oddK   : odd n -> proot r n a ^+ n = a                             *)
(*   proot_oddM   : odd n -> proot r n (a * b) = proot r n a * proot r n b    *)
(*   proot_oddX   : odd n -> proot r n (a ^+ m) = proot r n a ^+ m            *)
(*   proot_odd_exprMn : odd (n * k) -> proot r (n * k) a ^+ k = proot r n a   *)
(*   proot_sqr    : proot r 2 (a ^+ 2) = `|a| (also normr_proot, reversed)    *)
(*   normr_rootR  : `|a| = rootR 2 (a ^+ 2) on an rcfType                     *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts RootR.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Record realroot (F : numFieldType) (r : posroot F) : Prop := RealRoot {
  realroot_odd : oddroot r;
  realroot_real : forall a : F, a \is Num.real
}.

Lemma realroot_of (F : realFieldType) (r : posroot F) (o : oddroot r) :
  realroot r.
Proof. by split=> // a; apply: num_real. Qed.

Section RealRootFacts.

Variables (F : numFieldType) (r : posroot F) (rl : realroot r).

Implicit Types (a b : F) (n m k : nat).

Let o := realroot_odd rl.

Lemma realroot_ge0 n a : (0 < n)%N -> ~~ odd n -> 0 <= a ^+ n.
Proof. by move=> _ En; apply: real_exprn_even_ge0 (realroot_real rl a) En. Qed.

Lemma proot_oddK n a : odd n -> proot r n a ^+ n = a.
Proof. by move=> On; apply: (prootNK o On (realroot_real rl a)). Qed.

(* a = a' or a = - a' with 0 <= a' *)
Lemma realroot_sign a : exists2 a', 0 <= a' & a = a' \/ a = - a'.
Proof.
have [a0|a0] := real_ge0P (realroot_real rl a); first by exists a; [|left].
by exists (- a); [rewrite oppr_ge0 ltW|right; rewrite opprK].
Qed.

Lemma proot_oddM n a b : odd n ->
  proot r n (a * b) = proot r n a * proot r n b.
Proof.
move=> On; have n0 : (0 < n)%N by case: n On.
have [a' a0 [->|->]] := realroot_sign a;
  have [b' b0 [->|->]] := realroot_sign b.
- by rewrite prootM.
- by rewrite mulrN !(prootN o) // prootM // mulrN.
- by rewrite mulNr !(prootN o) // prootM // mulNr.
by rewrite mulrNN !(prootN o) // prootM // mulrNN.
Qed.

Lemma proot_oddX n m a : odd n -> proot r n (a ^+ m) = proot r n a ^+ m.
Proof.
move=> On; have n0 : (0 < n)%N by case: n On.
elim: m => [|m IH]; first by rewrite !expr0 proot_1.
by rewrite !exprS proot_oddM // IH.
Qed.

Lemma proot_odd_exprMn n k a : odd (n * k) ->
  proot r (n * k) a ^+ k = proot r n a.
Proof.
rewrite oddM => /andP[On Ok].
have n0 : (0 < n)%N by case: n On.
have k0 : (0 < k)%N by case: k Ok.
have [a' a0 [->|->]] := realroot_sign a; first by rewrite prootMn.
rewrite !(prootN o) ?oddM ?On // exprNn -signr_odd Ok expr1 mulN1r.
by rewrite prootMn.
Qed.

Lemma proot_sqr a : proot r 2 (a ^+ 2) = `|a|.
Proof.
by apply: proot_eq => //; rewrite real_normK // (realroot_real rl a).
Qed.

Lemma normr_proot a : `|a| = proot r 2 (a ^+ 2).
Proof. by rewrite proot_sqr. Qed.

End RealRootFacts.

Lemma rootR_realroot (R : rcfType) : realroot (rootR_posroot R).
Proof. exact: realroot_of (rootR_oddroot R). Qed.

Lemma normr_rootR (R : rcfType) (a : R) : `|a| = rootR 2 (a ^+ 2).
Proof. exact: (normr_proot (rootR_realroot R)). Qed.
