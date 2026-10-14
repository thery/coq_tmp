(******************************************************************************)
(* Rstruct: Stdlib's R as a mathcomp realClosedFieldType (needed by RootR.v). *)
(* Borrowed from mathcomp-analysis, reals_stdlib/Rstruct.v, cut right after   *)
(* the rcfType instance (From Coq -> From Stdlib, mathcomp_extra dropped).    *)
(* Same licence as the original (CeCILL-C).                                   *)
(*   RleP, RltP : reflect Stdlib's Rle, Rlt into mathcomp's <=, <             *)
(******************************************************************************)

(* This file is a modification of an eponymous file from the CoqApprox        *)
(* library. The header of the original file is reproduced below. Changes are  *)
(* part of the analysis library and enjoy the same licence as this library.   *)
(**
This file is part of the CoqApprox formalization of rigorous
polynomial approximation in Coq:
http://tamadi.gforge.inria.fr/CoqApprox/

Copyright (c) 2010-2013, ENS de Lyon and Inria.

This library is governed by the CeCILL-C license under French law and
abiding by the rules of distribution of free software. You can use,
modify and/or redistribute the library under the terms of the CeCILL-C
license as circulated by CEA, CNRS and Inria at the following URL:
http://www.cecill.info/

As a counterpart to the access to the source code and rights to copy,
modify and redistribute granted by the license, users are provided
only with a limited warranty and the library's author, the holder of
the economic rights, and the successive licensors have only limited
liability. See the COPYING file for more details.
*)

(**md**************************************************************************)
(* # Compatibility with the real numbers of Coq                               *)
(******************************************************************************)

From Stdlib Require Import ZArith Rdefinitions Raxioms RIneq Rbasic_fun Zwf.
From Stdlib Require Import Epsilon FunctionalExtensionality.
From Stdlib Require Import Ranalysis1 Rsqrt_def.
From Stdlib Require Import Rtrigo1 Reals.
From mathcomp Require Import all_ssreflect ssralg poly mxpoly ssrnum.
From mathcomp Require Import archimedean.
From HB Require Import structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope R_scope.

Lemma Req_EM_T (r1 r2 : R) : {r1 = r2} + {r1 <> r2}.
Proof.
case: (total_order_T r1 r2) => [[r1Lr2 | <-] | r1Gr2].
- by right=> r1Er2; case: (Rlt_irrefl r1); rewrite {2}r1Er2.
- by left.
by right=> r1Er2; case: (Rlt_irrefl r1); rewrite {1}r1Er2.
Qed.

Definition eqr (r1 r2 : R) : bool :=
  if Req_EM_T r1 r2 is left _ then true else false.

Lemma eqrP : Equality.axiom eqr.
Proof.
by move=> r1 r2; rewrite /eqr; case: Req_EM_T=> H; apply: (iffP idP).
Qed.

#[hnf] HB.instance Definition _ := hasDecEq.Build R eqrP.

Fact inhR : inhabited R.
Proof. exact: (inhabits 0). Qed.

Definition pickR (P : pred R) (n : nat) :=
  let x := epsilon inhR P in if P x then Some x else None.

Fact pickR_some P n x : pickR P n = Some x -> P x.
Proof. by rewrite /pickR; case: (boolP (P _)) => // Px [<-]. Qed.

Fact pickR_ex (P : pred R) :
  (exists x : R, P x) -> exists n, pickR P n.
Proof. by rewrite /pickR; move=> /(epsilon_spec inhR)->; exists 0%N. Qed.

Fact pickR_ext (P Q : pred R) : P =1 Q -> pickR P =1 pickR Q.
Proof.
move=> PEQ n; rewrite /pickR; set u := epsilon _ _; set v := epsilon _ _.
suff->: u = v by rewrite PEQ.
by congr epsilon; apply: functional_extensionality=> x; rewrite PEQ.
Qed.

#[hnf]
HB.instance Definition _ := hasChoice.Build R pickR_some pickR_ex pickR_ext.

Fact RplusA : associative (Rplus).
Proof. by move=> *; rewrite Rplus_assoc. Qed.

#[hnf]
HB.instance Definition _ := GRing.isZmodule.Build R
  RplusA Rplus_comm Rplus_0_l Rplus_opp_l.

Fact RmultA : associative Rmult.
Proof. by move=> *; rewrite Rmult_assoc. Qed.

Fact R1_neq_0 : R1 != R0.
Proof. by apply/eqP/R1_neq_R0. Qed.

#[hnf]
HB.instance Definition _ := GRing.Zmodule_isRing.Build R
  RmultA Rmult_1_l Rmult_1_r Rmult_plus_distr_r Rmult_plus_distr_l R1_neq_0.

#[hnf]
HB.instance Definition _ := GRing.Ring_hasCommutativeMul.Build R Rmult_comm.

Import Monoid.

HB.instance Definition _ := isComLaw.Build R 0 Rplus
  RplusA Rplus_comm Rplus_0_l.

HB.instance Definition _ := isComLaw.Build R 1 Rmult
  RmultA Rmult_comm Rmult_1_l.

HB.instance Definition _ := isMulLaw.Build R 0 Rmult Rmult_0_l Rmult_0_r.
HB.instance Definition _ := isAddLaw.Build R Rmult Rplus
  Rmult_plus_distr_r Rmult_plus_distr_l.

Definition unit_R r := r != 0.

Lemma intro_unit_R x y : y * x = 1 /\ x * y = 1 -> unit_R x.
Proof.
move=> [yx_eq1 _]; apply: contra_eqN yx_eq1 => /eqP->.
by rewrite Rmult_0_r eq_sym R1_neq_0.
Qed.

Section Rinvx.

Let Rinvx r := if (r != 0) then / r else r.

Let neq0_RinvxE x : x != 0 -> Rinv x = Rinvx x.
Proof. by move=> x_neq0; rewrite -[RHS]/(if _ then _ else _) x_neq0. Qed.

Let RinvxE x : Rinv x = Rinvx x.
Proof.
have [->| ] := eqVneq x R0; last exact: neq0_RinvxE.
rewrite /GRing.inv /GRing.mul /= /Rinvx eqxx /=.
rewrite RinvImpl.Rinv_def; case: Req_appart_dec => //.
by move=> /[dup] -[] /Rlt_irrefl.
Qed.

Lemma RmultRinv : {in unit_R, left_inverse 1 Rinv Rmult}.
Proof.
move=> r; rewrite RinvxE -topredE /unit_R /Rinvx => /= rNZ /=.
by rewrite rNZ Rinv_l //; apply/eqP.
Qed.

Lemma RinvRmult : {in unit_R, right_inverse 1 Rinv Rmult}.
Proof.
move=> r; rewrite RinvxE -topredE /unit_R /Rinvx => /= rNZ /=.
by rewrite rNZ Rinv_r //; apply/eqP.
Qed.

Lemma Rinv_out : {in predC unit_R, Rinv =1 id}.
Proof. by move=> x; rewrite inE/= RinvxE /Rinvx -if_neg => ->. Qed.

End Rinvx.

#[deprecated(note="To be removed. Use GRing.inv instead.")]
Definition Rinvx := Rinv.

#[hnf]
HB.instance Definition _ := GRing.Ring_hasMulInverse.Build R
  RmultRinv RinvRmult intro_unit_R Rinv_out.

Lemma R_idomainMixin x y : x * y = 0 -> (x == 0) || (y == 0).
Proof. by move=> /Rmult_integral []->; rewrite eqxx ?orbT. Qed.

#[hnf]
HB.instance Definition _ := GRing.ComUnitRing_isIntegral.Build R
  R_idomainMixin.

Lemma R_fieldMixin : GRing.field_axiom R. Proof. by []. Qed.
HB.instance Definition _ := GRing.UnitRing_isField.Build R R_fieldMixin.

(** Reflect the order on the reals to bool *)

Definition Rleb r1 r2 := if Rle_dec r1 r2 is left _ then true else false.
Definition Rltb r1 r2 := Rleb r1 r2 && (r1 != r2).
Definition Rgeb r1 r2 := Rleb r2 r1.
Definition Rgtb r1 r2 := Rltb r2 r1.

Lemma RlebP r1 r2 : reflect (r1 <= r2) (Rleb r1 r2).
Proof. by rewrite /Rleb; apply: (iffP idP); case: Rle_dec. Qed.

Lemma RltbP r1 r2 : reflect (r1 < r2) (Rltb r1 r2).
Proof.
rewrite /Rltb /Rleb; apply: (iffP idP); case: Rle_dec=> //=.
- by case=> // r1Er2 /eqP[].
- by move=> _ r1Lr2; apply/eqP/Rlt_not_eq.
by move=> Nr1Lr2 r1Lr2; case: Nr1Lr2; left.
Qed.

Section ssreal_struct.

Import GRing.Theory.
Import Num.Theory.
Import Num.Def.

Local Open Scope R_scope.

Lemma Rleb_norm_add x y : Rleb (Rabs (x + y)) (Rabs x + Rabs y).
Proof. by apply/RlebP/Rabs_triang. Qed.

Lemma addr_Rgtb0 x y : Rltb 0 x -> Rltb 0 y -> Rltb 0 (x + y).
Proof. by move/RltbP=> Hx /RltbP Hy; apply/RltbP/Rplus_lt_0_compat. Qed.

Lemma Rnorm0_eq0 x : Rabs x = 0 -> x = 0.
Proof. by move=> H; case: (x == 0) /eqP=> // /Rabs_no_R0. Qed.

Lemma Rleb_leVge x y : Rleb 0 x -> Rleb 0 y -> (Rleb x y) || (Rleb y x).
Proof.
move/RlebP=> Hx /RlebP Hy; case: (Rlt_le_dec x y).
by move/Rlt_le/RlebP=> ->.
by move/RlebP=> ->; rewrite orbT.
Qed.

Lemma RnormM : {morph Rabs : x y / x * y}.
Proof. exact: Rabs_mult. Qed.

Lemma Rleb_def x y : (Rleb x y) = (Rabs (y - x) == y - x).
Proof.
apply/(sameP (RlebP x y))/(iffP idP)=> [/eqP H| /Rle_minus H].
  apply: Rminus_le; rewrite -Ropp_minus_distr.
  apply/Rge_le/Ropp_0_le_ge_contravar.
  by rewrite -H; apply: Rabs_pos.
apply/eqP/Rabs_pos_eq.
rewrite -Ropp_minus_distr.
by apply/Ropp_0_ge_le_contravar/Rle_ge.
Qed.

Lemma Rltb_def x y : (Rltb x y) = (y != x) && (Rleb x y).
Proof.
apply/(sameP (RltbP x y))/(iffP idP).
  case/andP=> /eqP H /RlebP/Rle_not_gt H2.
  by case: (Rtotal_order x y)=> // [][] // /esym.
move=> H; apply/andP; split; [apply/eqP|apply/RlebP].
  exact: Rgt_not_eq.
exact: Rlt_le.
Qed.

HB.instance Definition _ := Num.IntegralDomain_isNumRing.Build R
  Rleb_norm_add addr_Rgtb0 Rnorm0_eq0 Rleb_leVge RnormM Rleb_def Rltb_def.

Lemma RleP : forall x y, reflect (Rle x y) (x <= y)%R.
Proof. exact: RlebP. Qed.
Lemma RltP : forall x y, reflect (Rlt x y) (x < y)%R.
Proof. exact: RltbP. Qed.

Lemma Rreal_axiom (x : R) : (0 <= x)%R || (x <= 0)%R.
Proof.
case: (Rle_dec 0 x)=> [/RleP ->|] //.
by move/Rnot_le_lt/Rlt_le/RleP=> ->; rewrite orbT.
Qed.

Lemma R_total : total (<=%O : rel R).
Proof.
move=> x y; case: (Rle_lt_dec x y) => [/RleP -> //|/Rlt_le/RleP ->];
  by rewrite orbT.
Qed.

HB.instance Definition _ := Order.POrder_isTotal.Build _ R R_total.

Lemma Rarchimedean_axiom : Num.archimedean_axiom R.
Proof.
move=> x; exists (Z.abs_nat (up x) + 2)%N.
have [Hx1 Hx2]:= (archimed x).
have Hz (z : Z): z = (z - 1 + 1)%Z by rewrite Zplus_comm Zplus_minus.
have Zabs_nat_Zopp z : Z.abs_nat (- z)%Z = Z.abs_nat z by case: z.
apply/RltbP/Rabs_def1.
  apply: (Rlt_trans _ ((Z.abs_nat (up x))%:R)%R); last first.
    rewrite -[((Z.abs_nat _)%:R)%R]Rplus_0_r mulrnDr.
    by apply/Rplus_lt_compat_l/Rlt_0_2.
  apply: (Rlt_le_trans _ (IZR (up x)))=> //.
  elim/(well_founded_ind (Zwf_well_founded 0)): (up x) => z IHz.
  case: (Z_lt_le_dec 0 z) => [zp | zn].
    rewrite [z]Hz plus_IZR Zabs_nat_Zplus //; last exact: Zlt_0_le_0_pred.
    rewrite plusE mulrnDr.
    apply/Rplus_le_compat_r/IHz; split; first exact: Zlt_le_weak.
    exact: Zlt_pred.
  apply: (Rle_trans _ (IZR 0)); first exact: IZR_le.
  by apply/RlebP/(ler0n R (Z.abs_nat z)).
apply: (Rlt_le_trans _ (IZR (up x) - 1)).
  apply: Ropp_lt_cancel; rewrite Ropp_involutive.
  rewrite Ropp_minus_distr /Rminus -opp_IZR -{2}(Z.opp_involutive (up x)).
  elim/(well_founded_ind (Zwf_well_founded 0)): (- up x)%Z => z IHz .
  case: (Z_lt_le_dec 0 z) => [zp | zn].
  rewrite [z]Hz Zabs_nat_Zopp plus_IZR.
  rewrite Zabs_nat_Zplus //; last exact: Zlt_0_le_0_pred.
    rewrite plusE -Rplus_assoc -addnA [(_ + 2)%N]addnC addnA mulrnDr.
    apply: Rplus_lt_compat_r; rewrite -Zabs_nat_Zopp.
    apply: IHz; split; first exact: Zlt_le_weak.
    exact: Zlt_pred.
  apply: (Rle_lt_trans _ 1).
    rewrite -{2}[1]Rplus_0_r; apply: Rplus_le_compat_l.
    by rewrite -/(IZR 0); apply: IZR_le.
  rewrite mulrnDr; apply: (Rlt_le_trans _ 2).
    by rewrite -{1}[1]Rplus_0_r; apply/Rplus_lt_compat_l/Rlt_0_1.
  rewrite -[2]Rplus_0_l; apply: Rplus_le_compat_r.
  by apply/RlebP/(ler0n R (Z.abs_nat _)).
apply: Rminus_le.
rewrite /Rminus Rplus_assoc [- _ + _]Rplus_comm -Rplus_assoc -!/(Rminus _ _).
exact: Rle_minus.
Qed.

HB.instance Definition _ := Num.NumDomain_bounded_isArchimedean.Build R
  Rarchimedean_axiom.

(** Here are the lemmas that we will use to prove that R has
the rcfType structure. *)

Lemma continuity_eq f g : f =1 g -> continuity f -> continuity g.
Proof.
move=> Hfg Hf x eps Heps.
have [y [Hy1 Hy2]]:= Hf x eps Heps.
by exists y; split=> // z; rewrite -!Hfg; exact: Hy2.
Qed.

Lemma continuity_sum (I : finType) F (P : pred I):
(forall i, P i -> continuity (F i)) ->
continuity (fun x => (\sum_(i | P i) ((F i) x)))%R.
Proof.
move=> H; elim: (index_enum I)=> [|a l IHl].
  set f:= fun _ => _.
  have Hf: (fun x=> 0) =1 f by move=> x; rewrite /f big_nil.
  by apply: (continuity_eq Hf); exact: continuity_const.
set f := fun _ => _.
case Hpa: (P a).
  have Hf: (fun x => F a x + \sum_(i <- l | P i) F i x)%R =1 f.
    by move=> x; rewrite /f big_cons Hpa.
  apply: (continuity_eq Hf); apply: continuity_plus=> //.
  exact: H.
have Hf: (fun x => \sum_(i <- l | P i) F i x)%R =1 f.
  by move=> x; rewrite /f big_cons Hpa.
exact: (continuity_eq Hf).
Qed.

Lemma continuity_exp f n: continuity f -> continuity (fun x => (f x)^+ n)%R.
Proof.
move=> Hf; elim: n=> [|n IHn]; first exact: continuity_const.
set g:= fun _ => _.
have Hg: (fun x=> f x * f x ^+ n)%R =1 g.
  by move=> x; rewrite /g exprS.
by apply: (continuity_eq Hg); exact: continuity_mult.
Qed.

Lemma Rreal_closed_axiom : Num.real_closed_axiom R.
Proof.
move=> p a b; rewrite !le_eqVlt.
case Hpa: ((p.[a])%R == 0%R).
  by move=> ? _ ; exists a=> //; rewrite lexx le_eqVlt.
case Hpb: ((p.[b])%R == 0%R).
  by move=> ? _; exists b=> //; rewrite lexx le_eqVlt andbT.
case Hab: (a == b).
  by move=> _; rewrite (eqP Hab) eq_sym Hpb (ltNge 0) /=; case/andP=> /ltW ->.
rewrite eq_sym Hpb /=; clear=> /RltbP Hab /andP [] /RltbP Hpa /RltbP Hpb.
suff Hcp: continuity (fun x => (p.[x])%R).
  have [z [[Hza Hzb] /eqP Hz2]]:= IVT _ a b Hcp Hab Hpa Hpb.
  by exists z=> //; apply/andP; split; apply/RlebP.
rewrite -[p]coefK poly_def.
set f := fun _ => _.
have Hf: (fun (x : R) => \sum_(i < size p) (p`_i * x^+i))%R =1 f.
  move=> x; rewrite /f horner_sum.
  by apply: eq_bigr=> i _; rewrite hornerZ hornerXn.
apply: (continuity_eq Hf); apply: continuity_sum=> i _.
apply:continuity_scal; apply: continuity_exp=> x esp Hesp.
by exists esp; split=> // y [].
Qed.

HB.instance Definition _ := Num.RealField_isClosed.Build R Rreal_closed_axiom.

End ssreal_struct.
