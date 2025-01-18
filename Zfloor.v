(******************************************************************************)
(*                                                                            *)
(*  Zfloor x        == floor fonction : R -> Z                                *)
(*  Zceil x         == ceil fonction : R -> Z                                 *)
(*                                                                            *)
(*  rify            == tactic that turns a goal in Z into a goal in R         *)
(*  Zfloor_tac      == propagate + and - on Zfloor and add extra hyps         *)
(*  IZR_lra x       == lra + IZR                                              *)
(******************************************************************************)

From mathcomp Require Import ssreflect.
Require Import Reals Lra Lia.

Open Scope R_scope.

Definition Zfloor (x : R) := (up x - 1)%Z.

Lemma up_Zfloor x : up x = (Zfloor x + 1)%Z.
Proof. rewrite /Zfloor; lia. Qed.

Lemma IZR_up_Zfloor x : IZR (up x) = IZR (Zfloor x) + 1.
Proof. by rewrite up_Zfloor plus_IZR. Qed.

Lemma Zfloor_bound x : IZR (Zfloor x) <= x < IZR (Zfloor x) + 1.
Proof.
rewrite /Zfloor minus_IZR /=.
have [] := archimed x; lra.
Qed.

Lemma Zfloor_lub (z : Z) x : IZR z <= x -> (z <= Zfloor x)%Z.
Proof.
move=> H.
suff: (z < Zfloor x + 1)%Z by lia.
apply: lt_IZR; rewrite plus_IZR /=.
have [] := Zfloor_bound x; lra.
Qed.

Lemma Zfloor_eq (z : Z) x :  IZR z <= x < IZR z + 1 -> Zfloor x = z.
Proof.
move=> xB.
have ZxB := Zfloor_bound x.
suff : (Zfloor x < z + 1 /\ z <= Zfloor x)%Z by lia.
split; last by apply: Zfloor_lub; lra.
apply : lt_IZR; rewrite plus_IZR /=; lra.
Qed.

Lemma ZfloorZ (z : Z) : Zfloor (IZR z) = z.
Proof. apply: Zfloor_eq; lra. Qed.


Lemma ZfloorNZ (z : Z) : Zfloor (- IZR z) = (- z)%Z.
Proof. by rewrite -opp_IZR ZfloorZ. Qed.

Inductive compare_R_Z (m n : R) (z1 z2 : Z) : Z -> Set :=
   Compare_R_Z_Le : (m <= n)%R -> compare_R_Z m n z1 z2 z1
|  Compare_R_Z_Gt : (n < m)%R -> compare_R_Z m n z1 z2 z2.
 
Lemma ZfloorD_cond r1 r2 : 
  compare_R_Z (IZR (Zfloor r1) + IZR (Zfloor r2) + 1) (r1 + r2)
  (Zfloor r1 + Zfloor r2 + 1)%Z
  (Zfloor r1 + Zfloor r2)%Z  
  (Zfloor (r1 + r2)).
Proof.
have [Zr1 Zr2] := (Zfloor_bound r1, Zfloor_bound r2).
case: (Rle_dec (IZR (Zfloor r1) + IZR (Zfloor r2) + 1) (r1 + r2)) => H /=.
  have -> : Zfloor (r1 + r2) = (Zfloor r1 + Zfloor r2 + 1)%Z.
    by apply: Zfloor_eq; rewrite plus_IZR plus_IZR /=; lra.
  by apply: Compare_R_Z_Le.
have -> : Zfloor (r1 + r2) = (Zfloor r1 + Zfloor r2)%Z.
  by apply: Zfloor_eq; rewrite plus_IZR; lra.
by apply: Compare_R_Z_Gt; lra.
Qed.

(*
Lemma ZfloorD_cond r1 r2 : 
  if Rle_dec (IZR (Zfloor r1) + IZR (Zfloor r2) + 1) (r1 + r2) is left _
  then Zfloor (r1 + r2) = (Zfloor r1 + Zfloor r2 + 1)%Z
  else  Zfloor (r1 + r2) = (Zfloor r1 + Zfloor r2)%Z.  
Proof.
have [Zr1 Zr2] := (Zfloor_bound r1, Zfloor_bound r2).
case: Rle_dec => H /=.
  apply: Zfloor_eq; rewrite plus_IZR plus_IZR /=; lra.
apply: Zfloor_eq; rewrite plus_IZR; lra.
Qed.
*)

Definition Zceil (x : R) := (- Zfloor (- x))%Z.

Theorem Zceil_bound x : (IZR (Zceil x) - 1 < x <= IZR (Zceil x))%R.
Proof.
rewrite /Zceil; have := Zfloor_bound (- x).
by rewrite !opp_IZR; lra.
Qed.

Theorem Zfloor_ceil_bound x : (IZR (Zfloor x) <= x <= IZR (Zceil x))%R.
Proof.
by have := Zfloor_bound x; have := Zceil_bound x; lra.
Qed.

Theorem ZceilN x : (Zceil (- x) = - Zfloor x)%Z.
Proof. by rewrite /Zceil Ropp_involutive. Qed.

Theorem ZfloorN x : (Zfloor (- x) = - Zceil x)%Z.
Proof. rewrite /Zceil; lia. Qed.

Lemma ZceilD_cond r1 r2 : 
  compare_R_Z (r1 + r2) (IZR (Zceil r1) + IZR (Zceil r2) - 1) 
  (Zceil r1 + Zceil r2 - 1)
  (Zceil r1 + Zceil r2) (Zceil (r1 + r2)).  
Proof.
rewrite /Zceil !Ropp_plus_distr; case: ZfloorD_cond => H.
  have -> :  (- Zfloor (- r1) + - Zfloor (- r2) - 1 = 
            - (Zfloor (- r1) + Zfloor (- r2) + 1))%Z by lia.
  by apply: Compare_R_Z_Le; rewrite !opp_IZR; lra.
have -> :  
  (- Zfloor (- r1) + - Zfloor (- r2) = - (Zfloor (- r1) + Zfloor (- r2)))%Z.
  by lia.
by apply: Compare_R_Z_Gt; rewrite !opp_IZR; lra.
Qed.

(* 
Lemma ZceilD_cond r1 r2 : 
  if Rle_dec (r1 + r2) (IZR (Zceil r1) + IZR (Zceil r2) - 1) is left _
  then Zceil (r1 + r2) = (Zceil r1 + Zceil r2 - 1)%Z 
  else Zceil (r1 + r2) = (Zceil r1 + Zceil r2)%Z.  
Proof.
have := ZfloorD_cond (- r1) (- r2).
rewrite !ZfloorN !opp_IZR -!Ropp_plus_distr Ropp_involutive !ZfloorN.
by do 2 case: Rle_dec; try lia; lra.
Qed.
*)

Lemma ZfloorB_cond r1 r2 : 
  compare_R_Z (IZR (Zfloor r1) - IZR (Zceil r2) + 1) (r1 - r2) 
  (Zfloor r1 - Zceil r2 + 1)
  (Zfloor r1 - Zceil r2)  
  (Zfloor (r1 - r2)).
Proof.
rewrite /Zceil; case: ZfloorD_cond => H.
  have -> :  (Zfloor r1 - - Zfloor (- r2) + 1 = Zfloor r1 + Zfloor (- r2) + 1)%Z
    by lia.
  by apply: Compare_R_Z_Le; rewrite !opp_IZR; lra.
have -> :  (Zfloor r1 - - Zfloor (- r2) = Zfloor r1 + Zfloor (- r2))%Z 
  by lia.
by apply: Compare_R_Z_Gt; rewrite !opp_IZR; lra.
Qed.

(* 
Lemma ZfloorB_cond r1 r2 : 
  if Rle_dec (IZR (Zfloor r1) - IZR (Zceil r2) + 1) (r1 - r2) is left _
  then Zfloor (r1 - r2) = (Zfloor r1 - Zceil r2 + 1)%Z
  else  Zfloor (r1 - r2) = (Zfloor r1 - Zceil r2)%Z.  
Proof. by have := ZfloorD_cond r1 (- r2); rewrite !ZfloorN !opp_IZR. Qed.
*)

Lemma ZceilB_cond r1 r2 : 
  compare_R_Z (r1 - r2) (IZR (Zceil r1) - IZR (Zfloor r2) - 1) 
  (Zceil r1 - Zfloor r2 - 1) 
  (Zceil r1 - Zfloor r2) 
  (Zceil (r1 - r2)).
Proof.
case: ZceilD_cond => H.
  have -> :  (Zceil r1 - Zfloor r2 - 1 = Zceil r1 + Zceil (- r2) - 1)%Z
    by rewrite ZceilN; lia.
  by apply: Compare_R_Z_Le; rewrite ZceilN opp_IZR in H; lra.
have -> :  (Zceil r1 - Zfloor r2  = Zceil r1 + Zceil (- r2))%Z.
  by rewrite ZceilN; lia.
by apply: Compare_R_Z_Gt; rewrite ZceilN opp_IZR in H; lra.
Qed.

(*
Lemma ZceilB_cond r1 r2 : 
  if Rle_dec (r1 - r2) (IZR (Zceil r1) - IZR (Zfloor r2) - 1) is left _
  then Zceil (r1 - r2) = (Zceil r1 - Zfloor r2 - 1)%Z 
  else Zceil (r1 - r2) = (Zceil r1 - Zfloor r2)%Z.  
Proof. by have := ZceilD_cond r1 (- r2); rewrite !ZceilN !opp_IZR. Qed.
*)

Ltac clean_IZR := 
 rewrite ?(opp_IZR, plus_IZR, minus_IZR) ?IZR_up_Zfloor 
          ?(ZfloorZ, ZfloorNZ, opp_IZR).

Lemma IZR_neq x y  : (x <> y :> Z) -> IZR x <> IZR y.
Proof. by move=> Hx Hy; case: Hx; apply: eq_IZR. Qed.


(* Only handle /\ should use Trocq instead *)
Ltac rify :=  
(* Transform the conclusion *)
try (intros; repeat split; 
match goal with 
  |- ~ _ => unfold not; intros
| |- (_ >= _)%Z => apply/Z.le_ge/le_IZR 
| |- (_ > _)%Z => apply/Z.lt_gt/lt_IZR 
| |- (_ <= _)%Z => apply/le_IZR 
| |- (_ < _)%Z => apply/lt_IZR 
| |- (_ = _)%Z => apply/eq_IZR 
end; clean_IZR);
(* Transform the conclusion*)
repeat (match goal with 
  H : _ /\ _ |- _ => destruct H 
| H : (_ >= _)%Z |- _ => generalize (Z.ge_le _ _ H); clear H; intro H
| H : (_ > _)%Z |- _ => generalize (Z.gt_lt _ _ H); clear H; intro H
| H : (_ <= _)%Z |- _ => generalize (IZR_le _ _ H); clear H
| H : (_ < _)%Z |- _ => generalize (IZR_lt _ _ H); clear H
| H : (_ = _ :> Z) |- _ => generalize (IZR_eq _ _ H); clear H
| H : (_ <> _ :> Z) |- _ => generalize (IZR_neq _ _ H); clear H
end); clean_IZR.

Goal forall x y,  ((x <> y /\ x >= y) -> y < x)%Z.
rify.
lra.
Qed.

Ltac Zfloor_tac :=
 rify; rewrite /Zceil;
 (* Propagate + over Zfloor *)
 repeat (case: ZfloorD_cond; clean_IZR); 
 (* Add bound assumptions *)
 repeat (match goal with 
   |- context [IZR (Zfloor ?x)] => 
      have := Zfloor_bound x;
      let v := fresh "zv" in set v := Zfloor x
 end).

(* Hiding synomym *)
Definition IZR1 := IZR.

Lemma IZR1_Zpos z : IZR (Zpos z) = IZR1 (Zpos z).
Proof. by []. Qed.

Lemma IZR1_Zneg z : IZR (Zneg z) = IZR1 (Zneg z).
Proof. by []. Qed.

Lemma IZR1_Z0 : IZR 0 = IZR1 0.
Proof. by []. Qed.

(* IZR -> IZR1 forall constant *)
Ltac change_IZR_const := rewrite ?(IZR1_Zpos, IZR1_Zneg, IZR1_Z0).

Definition Accu_IZR (l : list R) := True.

(* Box equation *)
Lemma IZR_eqE z1 z2 : IZR z1 - 1 < IZR z2 < IZR z1 + 1 -> IZR z1 = IZR z2.
Proof.
rewrite -minus_IZR -plus_IZR => [] [/lt_IZR ? /lt_IZR ?].
by apply: IZR_eq; lia.
Qed.

Ltac gen_IZR_eqsv v l :=
  match l with 
   cons ?v1 ?l1 =>  
    have : v - 1 < v1 < v + 1 -> v = v1 by apply: IZR_eqE; gen_IZR_eqsv v l1
  | _ => idtac
  end.

Ltac gen_IZR_eqs l :=
  match l with 
   cons ?v1 ?l1 => gen_IZR_eqsv v1 l1; gen_IZR_eqs l1 
  | _ => idtac
  end.

(* A preprocessor for lra that know IZR *)
Ltac IZR_lra :=
  (* pop all assumptions that talk about IZR *)
  repeat (match goal with 
    H : context[IZR _] |- _ => generalize H; clear H end); 
  (* hide IZR constant *)
  change_IZR_const;
  (* Give a name to all IZR *)
  have Hl : Accu_IZR nil by [];
  repeat (match goal with 
    H : Accu_IZR ?l |- context [IZR ?x] => 
      let v := fresh "zl" in set v := IZR x; clear H; 
      let nl := constr:(cons v l) in (have H : Accu_IZR nl by [])
   end);
  (* show IZR constants *)
  rewrite /IZR1;
  (* Generate the box equation for all IZR *)
  (match
     goal with 
    H : Accu_IZR ?l |- _ => gen_IZR_eqs l; clear H 
   end);
  (* call lra *)
  lra.

(* Some Test *)
Goal forall z1 z2 z3, Zfloor (IZR z1 - IZR z2 + IZR z3)%R = (z1 - z2 + z3)%Z.
Proof.
Zfloor_tac; IZR_lra.
Qed.

Goal forall (z : Z) x, IZR z <= x -> (z <= Zfloor x)%Z.
Proof.
Zfloor_tac; IZR_lra.
Qed.

Goal forall (z : Z) x,  IZR z <= x < IZR z + 1 -> Zfloor x = z.
Proof.
Zfloor_tac; IZR_lra.
Qed.
