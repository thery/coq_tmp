(******************************************************************************)
(* Cond: the checkers and the decision theorems.                              *)
(*   RadcanF N        == the normaliser over the number backend N : NUM       *)
(*                      (CondSimp, CondRoot, CondNorm, and this file)         *)
(*   radcan_check e1 e2 == Some cs when both sides have the same normal form  *)
(*                      under the conditions cs; radcan_check_odd,            *)
(*                      radcan_check_neg: the same in modes MOdd, MNeg (then  *)
(*                      MNegW); radcan_check_real: MRealA, then MReal; the    *)
(*                      irreducible basis (M16) is tried last                 *)
(*   radcan_check_negc  == MNegC, MNegCW (omega atoms merged across indices), *)
(*                      then radcan_check_neg                                 *)
(*   radcan_check_negs  == MNegS (MNegC, then sqrt 2, 3, 5 in roots of -1     *)
(*                      when the normal forms differ), then radcan_check_negc *)
(*   radcan_eq_cond, radcan_eq_cond0, radcan_eq_cond_odd,                     *)
(*   radcan_eq_cond_neg, radcan_eq_cond_real == the decision theorems         *)
(*   radcan_eq_cond_negc == the same for radcan_check_negc, given a negroot w *)
(*                      with the index law cycroot w (OmegaRoot2.v)           *)
(*   radcan_eq_cond_negs == the same for radcan_check_negs, given also       *)
(*                      sqrtroot w (OmegaRoot2.v)                             *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt ZArith Lia.
From Stdlib Require Import QArith_base Qreduction.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts Syntax Backend Mono Factor NF.
From Radcan Require Import Inverse Poly Ratio RealRoot OmegaRoot2.
From Radcan Require Export CondSimp CondRoot CondNorm.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module RadcanF (Import N : NUM).

Include CondNormF N.

(* the checkers: any posroot, with an oddroot, with a negroot; the    *)
(* irreducible basis (M16) is tried last                                *)
Definition radcan_check (e1 e2 : rexpr) : option (seq cond) :=
  if no_root e1 && no_root e2 then radcan_check0 e1 e2
  else if radcan_check_root MStd e1 e2 is Some cs then Some cs
  else radcan_check_rootf true MStd e1 e2.

Definition radcan_check_odd (e1 e2 : rexpr) : option (seq cond) :=
  if no_root e1 && no_root e2 then radcan_check0 e1 e2
  else if radcan_check_root MOdd e1 e2 is Some cs then Some cs
  else radcan_check_rootf true MOdd e1 e2.

(* MNegW (omega_n preferred to a flipped base) only when MNeg fails *)
Definition radcan_check_neg (e1 e2 : rexpr) : option (seq cond) :=
  if no_root e1 && no_root e2 then radcan_check0 e1 e2
  else if radcan_check_root MNeg e1 e2 is Some cs then Some cs
  else if radcan_check_root MNegW e1 e2 is Some cs then Some cs
  else if radcan_check_rootf true MNeg e1 e2 is Some cs then Some cs
  else radcan_check_rootf true MNegW e1 e2.

(* omega atoms merged across indices (needs the index law), then MNeg *)
Definition radcan_check_negc (e1 e2 : rexpr) : option (seq cond) :=
  if no_root e1 && no_root e2 then radcan_check0 e1 e2
  else if radcan_check_root MNegC e1 e2 is Some cs then Some cs
  else if radcan_check_root MNegCW e1 e2 is Some cs then Some cs
  else if radcan_check_rootf true MNegC e1 e2 is Some cs then Some cs
  else if radcan_check_rootf true MNegCW e1 e2 is Some cs then Some cs
  else radcan_check_neg e1 e2.

(* then sqrt 2, sqrt 3, sqrt 5 as sums of roots of -1 (Omega6) *)
Definition radcan_check_negs (e1 e2 : rexpr) : option (seq cond) :=
  if no_root e1 && no_root e2 then radcan_check0 e1 e2
  else if radcan_check_root MNegS e1 e2 is Some cs then Some cs
  else if radcan_check_rootf true MNegS e1 e2 is Some cs then Some cs
  else radcan_check_negc e1 e2.

(* real fields: absolute values first (MRealA), then MReal *)
Definition radcan_check_real (e1 e2 : rexpr) : option (seq cond) :=
  if no_root e1 && no_root e2 then radcan_check0 e1 e2
  else if radcan_check_root MRealA e1 e2 is Some cs then Some cs
  else if radcan_check_root MReal e1 e2 is Some cs then Some cs
  else if radcan_check_rootf true MRealA e1 e2 is Some cs then Some cs
  else radcan_check_rootf true MReal e1 e2.

Local Open Scope ring_scope.

(* The decision theorems used by the tactics *)

Theorem radcan_eq_cond (F : numFieldType) (r : posroot F) (env : seq F)
    e1 e2 cs :
  radcan_check e1 e2 = Some cs -> all_conds r env cs ->
  rinterp r env e1 = rinterp r env e2.
Proof.
rewrite /radcan_check; case: ifP => _ H Hc.
  exact: (radcan_check0_sound H (all_conds_bridge Hc)).
case/ocase_some: H => H; first exact: radcan_eq_cond_root H Hc.
exact: radcan_eq_cond_rootf H Hc.
Qed.

Theorem radcan_eq_cond_odd (F : numFieldType) (r : posroot F) (o : oddroot r)
    (env : seq F) e1 e2 cs :
  radcan_check_odd e1 e2 = Some cs -> all_conds r env cs ->
  rinterp r env e1 = rinterp r env e2.
Proof.
rewrite /radcan_check_odd; case: ifP => _ H Hc.
  exact: (radcan_check0_sound H (all_conds_bridge Hc)).
case/ocase_some: H => H; first exact: radcan_eq_cond_root H Hc.
exact: radcan_eq_cond_rootf H Hc.
Qed.

Theorem radcan_eq_odd (F : numFieldType) (r : posroot F) (o : oddroot r)
    (env : seq F) e1 e2 :
  radcan_check_odd e1 e2 = Some [::] -> rinterp r env e1 = rinterp r env e2.
Proof. by move/(radcan_eq_cond_odd o); apply. Qed.

Theorem radcan_eq_cond_neg (F : numFieldType) (r : posroot F) (w : negroot r)
    (env : seq F) e1 e2 cs :
  radcan_check_neg e1 e2 = Some cs -> all_conds r env cs ->
  rinterp r env e1 = rinterp r env e2.
Proof.
rewrite /radcan_check_neg; case: ifP => _ H Hc.
  exact: (radcan_check0_sound H (all_conds_bridge Hc)).
case/ocase_some: H => H; first exact: radcan_eq_cond_root H Hc.
case/ocase_some: H => H; first exact: radcan_eq_cond_root H Hc.
by case/ocase_some: H => H; exact: radcan_eq_cond_rootf H Hc.
Qed.

Theorem radcan_eq_neg (F : numFieldType) (r : posroot F) (w : negroot r)
    (env : seq F) e1 e2 :
  radcan_check_neg e1 e2 = Some [::] -> rinterp r env e1 = rinterp r env e2.
Proof. by move/(radcan_eq_cond_neg w); apply. Qed.

Theorem radcan_eq_cond_negc (F : numFieldType) (r : posroot F)
    (w : negroot r) (cy : cycroot w) (env : seq F) e1 e2 cs :
  radcan_check_negc e1 e2 = Some cs -> all_conds r env cs ->
  rinterp r env e1 = rinterp r env e2.
Proof.
have hw := cycroot_windex cy.
rewrite /radcan_check_negc; case: ifP => n0 H Hc.
  exact: (radcan_check0_sound H (all_conds_bridge Hc)).
case/ocase_some: H => H; first exact: radcan_eq_cond_root H Hc.
case/ocase_some: H => H; first exact: radcan_eq_cond_root H Hc.
case/ocase_some: H => H; first exact: radcan_eq_cond_rootf H Hc.
case/ocase_some: H => H; first exact: radcan_eq_cond_rootf H Hc.
move: H Hc; exact: (@radcan_eq_cond_neg F r w env e1 e2 cs).
Qed.

Theorem radcan_eq_negc (F : numFieldType) (r : posroot F) (w : negroot r)
    (cy : cycroot w) (env : seq F) e1 e2 :
  radcan_check_negc e1 e2 = Some [::] -> rinterp r env e1 = rinterp r env e2.
Proof. by move/(radcan_eq_cond_negc cy); apply. Qed.

Theorem radcan_eq_cond_negs (F : numFieldType) (r : posroot F)
    (w : negroot r) (cy : cycroot w) (sq : sqrtroot w) (env : seq F)
    e1 e2 cs :
  radcan_check_negs e1 e2 = Some cs -> all_conds r env cs ->
  rinterp r env e1 = rinterp r env e2.
Proof.
have hw := cycroot_windex cy; have hs := sqrtroot_wsqrt sq.
rewrite /radcan_check_negs; case: ifP => n0 H Hc.
  exact: (radcan_check0_sound H (all_conds_bridge Hc)).
case/ocase_some: H => H; first exact: radcan_eq_cond_root H Hc.
case/ocase_some: H => H; first exact: radcan_eq_cond_rootf H Hc.
by move: H Hc; exact: (@radcan_eq_cond_negc F r w cy env e1 e2 cs).
Qed.

Theorem radcan_eq_negs (F : numFieldType) (r : posroot F) (w : negroot r)
    (cy : cycroot w) (sq : sqrtroot w) (env : seq F) e1 e2 :
  radcan_check_negs e1 e2 = Some [::] -> rinterp r env e1 = rinterp r env e2.
Proof. by move/(radcan_eq_cond_negs cy sq); apply. Qed.

Theorem radcan_eq_cond_real (F : numFieldType) (r : posroot F)
    (rl : realroot r) (env : seq F) e1 e2 cs :
  radcan_check_real e1 e2 = Some cs -> all_conds r env cs ->
  rinterp r env e1 = rinterp r env e2.
Proof.
have o := realroot_odd rl.
rewrite /radcan_check_real; case: ifP => _ H Hc.
  exact: (radcan_check0_sound H (all_conds_bridge Hc)).
case/ocase_some: H => H; first exact: radcan_eq_cond_root H Hc.
case/ocase_some: H => H; first exact: radcan_eq_cond_root H Hc.
by case/ocase_some: H => H; exact: radcan_eq_cond_rootf H Hc.
Qed.

Theorem radcan_eq_real (F : numFieldType) (r : posroot F) (rl : realroot r)
    (env : seq F) e1 e2 :
  radcan_check_real e1 e2 = Some [::] -> rinterp r env e1 = rinterp r env e2.
Proof. by move/(radcan_eq_cond_real rl); apply. Qed.

Theorem radcan_eq (F : numFieldType) (r : posroot F) (env : seq F) e1 e2 :
  radcan_check e1 e2 = Some [::] -> rinterp r env e1 = rinterp r env e2.
Proof. by move/radcan_eq_cond; apply. Qed.

(* root-free goals, no posroot needed *)
Theorem radcan_eq_cond0 (F : numFieldType) (env : seq F) e1 e2 cs :
  no_root e1 -> no_root e2 -> radcan_check e1 e2 = Some cs ->
  all_conds0 env cs -> rinterp0 env e1 = rinterp0 env e2.
Proof.
by move=> n1 n2; rewrite /radcan_check n1 n2 /=; exact: radcan_check0_sound.
Qed.

End RadcanF.
