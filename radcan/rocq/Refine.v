(******************************************************************************)
(* Refine: refinement of the raw side conditions returned by radcan_check.    *)
(*   Pieces: RefPoly (data, polynomials), RefCheck (proved checker),          *)
(*   RefHeur (unverified search); examples in RefineEx.                       *)
(*   refine cs  == refine_raw cs when the checker verifies that every raw     *)
(*                 condition follows from the refined ones (implied), the     *)
(*                 raw conditions otherwise                                   *)
(*   all_rconds F rt env rs == the meaning of the refined conditions rs       *)
(*   refine_sound : all_rconds .. (refine cs) -> all_conds_gen rt env cs      *)
(*   radcan_eq_refined, radcan_eq_refined0 == decision theorems for radcan    *)
(* The reasoning holds in any numFieldType.                                   *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt ZArith Lia.
From Stdlib Require Import QArith_base Qreduction.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot Syntax Radcan.
From Radcan Require Export RefPoly RefCheck RefHeur.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* The refined conditions *)

Local Open Scope Q_scope.

Definition refine (cs : seq cond) : seq rcond :=
  let rs := refine_raw cs in
  if all (implied rs) cs then rs else map RRaw cs.

Local Close Scope Q_scope.
Local Open Scope ring_scope.

(* Meaning of the refined conditions *)

Definition babs (b : bound) : bound := let: (_, n, d) := b in (false, n, d).

Section Interp.
Variables (F : numFieldType) (B : Type) (bI : B -> F).
Variables (rt : nat -> F -> F) (env : seq F).

Definition apow (ak : rexpr * nat) : F :=
  let: (a, k) := ak in
  match k with 1%N => rinterp_gen rt env a | _ => rinterp_gen rt env a ^+ k end.

Definition mI (m : amono) : F :=
  if m is ak :: m' then foldl (fun acc ak => acc * apow ak) (apow ak) m' else 1.

(* the absolute value of a term *)
Definition tI (t : bound * amono) : F :=
  let: (c, m) := t in
  if m is [::] then bound_interp F (babs c)
  else if c is (_, 1%N, 1%N) then mI m else bound_interp F (babs c) * mI m.

Definition sideI (s : side) : F :=
  if s is t :: s' then
    foldl (fun acc t => if t.1.1.1 then acc - tI t else acc + tI t)
          (if t.1.1.1 then - tI t else tI t) s'
  else 0.

Definition rc_interp (r : rc B) : Prop :=
  match r with
  | RRaw c => cond_interp_gen rt env c
  | RLow s b i => if s then bI b < nth 0 env i else bI b <= nth 0 env i
  | RUpp s b i => if s then nth 0 env i < bI b else nth 0 env i <= bI b
  | RInt s1 b1 i s2 b2 =>
    let x := nth 0 env i in
    if s1 then (if s2 then bI b1 < x < bI b2 else bI b1 < x <= bI b2)
    else (if s2 then bI b1 <= x < bI b2 else bI b1 <= x <= bI b2)
  | RNeq i b => nth 0 env i != bI b
  | RCmp s l r => if s then sideI l < sideI r else sideI l <= sideI r
  | RDiff l r => sideI l != sideI r
  end.

Fixpoint all_rc (rs : seq (rc B)) : Prop :=
  match rs with
  | [::] => True
  | r :: rs' => if rs' is [::] then rc_interp r else rc_interp r /\ all_rc rs'
  end.

End Interp.

Notation rcond_interp F rt env r := (rc_interp (@bound_interp F) rt env r).
Notation all_rconds F rt env rs := (all_rc (@bound_interp F) rt env rs).

Section Proofs.
Variable F : numFieldType.

Local Arguments Qred : simpl never.
Local Arguments Qplus : simpl never.
Local Arguments Qmult : simpl never.
Local Arguments Qopp : simpl never.
Local Arguments Qinv : simpl never.

Variables (rt : nat -> F -> F) (env : seq F).
Local Notation ri := (rinterp_gen rt env).
Local Notation aeval := (aeval rt env).
Local Notation peval := (peval rt env).
Local Notation fsI := (fsI rt env).
Local Notation rimp1_sound := (@rimp1_sound F rt env).
Local Notation ptriv_sound := (@ptriv_sound F rt env).

(* the display *)

Lemma apowE ak : apow rt env ak = ri ak.1 ^+ ak.2.
Proof. by case: ak => a [|[|k]] //=; rewrite expr1. Qed.

Lemma mIE m : mI rt env m = aeval m.
Proof.
case: m => [|ak m] //=; rewrite apowE.
elim: m (ri ak.1 ^+ ak.2) => [|ak' m IH] x /=; first by rewrite mulr1.
by rewrite IH apowE mulrA.
Qed.

Lemma tIE t :
  (if t.1.1.1 then - tI rt env t else tI rt env t) =
  bound_interp F t.1 * aeval t.2.
Proof.
case: t => [[[neg n] d] m]; rewrite [_.1.1.1]/= [_.1]/= [_.2]/=.
have -> : tI rt env ((neg, n, d), m) = bound_interp F (false, n, d) * aeval m.
  rewrite /tI; case: m => [|ak m]; first by rewrite mulr1.
  rewrite mIE; case: n => [|[|n]] //; case: d => [|[|d]] //.
  by rewrite /bound_interp /= mul1r.
by case: neg; rewrite /bound_interp /= ?mulNr.
Qed.

Lemma sideIE s : sideI rt env s = peval (spoly s).
Proof.
case: s => [|t s] //=; rewrite padd_sound pterm_sound -tIE.
elim: s (if t.1.1.1 then - tI rt env t else tI rt env t) => [|t' s IH] x /=.
  by rewrite addr0.
rewrite IH padd_sound pterm_sound -tIE addrA; congr (_ + _).
by case: (t'.1.1.1).
Qed.

Local Notation rI := (rc_interp (@bound_interp F) rt env).
Local Arguments padd : simpl never.
Local Arguments pvar : simpl never.
Local Arguments pconst : simpl never.
Local Arguments pscale : simpl never.

Lemma rfacts_sound r : rI r -> fsI (rfacts r).
Proof.
have one f : kI f.1 (peval f.2) -> fsI [:: f] by move=> h f' [<-|].
case: r => [[e|e]|s b i|s b i|s1 b1 i s2 b2|i b|s l r|l r] /= h.
- by apply: one; rewrite /= pnorm_sound.
- by apply: one; rewrite /= pnorm_sound.
- by apply: one; exact: low_fact_sound.
- by apply: one; exact: upp_fact_sound.
- have [h1 h2] : (if s1 then bound_interp F b1 < nth 0 env i
                  else bound_interp F b1 <= nth 0 env i) /\
                 (if s2 then nth 0 env i < bound_interp F b2
                  else nth 0 env i <= bound_interp F b2).
    by case: s1 s2 h => [] [] /andP [].
  apply: fsI_cons; first exact: low_fact_sound.
  by apply: one; exact: upp_fact_sound.
- apply: one; rewrite /= padd_sound pconst_sound patom_sound Q2F_opp.
  by rewrite -bound_interpE subr_eq0.
- apply: one; rewrite /= padd_sound pscale_sound Q2Fm1 mulN1r -!sideIE.
  by case: s h => /=; rewrite ?subr_gt0 ?subr_ge0.
apply: one; rewrite /= padd_sound pscale_sound Q2Fm1 mulN1r -!sideIE.
by rewrite subr_eq0.
Qed.

Lemma comb1_sound fs strict P : fsI fs -> comb1 fs strict P ->
  if strict then 0 < peval P else 0 <= peval P.
Proof.
rewrite /comb1 => H; case: (fm_cert fs strict P) => [[ls c0]|] //.
exact: comb_check_sound.
Qed.

Lemma fcomb_sound fs f : fsI fs -> fcomb fs f -> kI f.1 (peval f.2).
Proof.
case: f => [[] P] H /=; try exact: comb1_sound.
case/orP => /(comb1_sound H) /=; first exact: lt0r_neq0.
by rewrite pscale_sound Q2Fm1 mulN1r oppr_gt0 => /ltr0_neq0.
Qed.

Lemma fimp_sound rs f :
  (forall r, List.In r rs -> rI r) -> fimp rs f -> kI f.1 (peval f.2).
Proof.
move=> H; have Hf : fsI (flatten (map rfacts rs)).
  elim: rs H => [|r rs IH] H /=; first by move=> ? [].
  apply: fsI_cat; first by apply: rfacts_sound; apply: H; left.
  by apply: IH => r0 h; apply: H; right.
case/or3P => [/ptriv_sound //||]; last exact: fcomb_sound.
elim: (flatten _) Hf => [|g gs IH] //= Hf /orP [Hg|Hgs].
  by apply: rimp1_sound Hg _; apply: Hf; left.
by apply: IH Hgs => g0 h; apply: Hf; right.
Qed.

Lemma implied_sound rs c :
  (forall r, List.In r rs -> rI r) -> implied rs c -> cond_interp_gen rt env c.
Proof.
move=> H; case: c => e /=.
  by move/(fimp_sound H) => /=; rewrite pnorm_sound.
case/orP; first by move/(fimp_sound H) => /=; rewrite pnorm_sound.
by apply: nzf_sound => q /(fimp_sound H).
Qed.

Lemma all_rcP rs :
  all_rc (@bound_interp F) rt env rs -> forall r, List.In r rs -> rI r.
Proof.
elim: rs => [|r rs IH] //=; case: rs IH => [|r' rs] IH.
  by move=> h r0 [<-|].
by case=> h1 /IH h2 r0 [<-|/h2].
Qed.

Lemma all_conds_genI cs :
  (forall c, List.In c cs -> cond_interp_gen rt env c) ->
  all_conds_gen rt env cs.
Proof.
elim: cs => [|c cs IH] //= H; case: cs IH H => [|c' cs] IH H.
  by apply: H; left.
split; first by apply: H; left.
by apply: IH => c0 Hc0; apply: H; right.
Qed.

Lemma all_rc_raw cs :
  all_rc (@bound_interp F) rt env (map RRaw cs) -> all_conds_gen rt env cs.
Proof. by elim: cs => [|c [|c' cs] IH] //= [h1 /IH]. Qed.

End Proofs.

(* Main theorem and the decision theorems for the tactic *)

Theorem refine_sound (F : numFieldType) (rt : nat -> F -> F) env cs :
  all_rconds F rt env (refine cs) -> all_conds_gen rt env cs.
Proof.
rewrite /refine; case: ifP => [Ha /all_rcP H|_]; last exact: all_rc_raw.
apply: all_conds_genI.
move: (refine_raw cs) H Ha => rs H.
elim: cs => [|c cs IH] //= /andP[Hc /IH Hcs] c0 [<-|/Hcs] //.
exact: implied_sound H Hc.
Qed.

Lemma all_conds_bridge_back (F : numFieldType) (r : posroot F) env cs :
  all_conds_gen (proot r) env cs -> all_conds r env cs.
Proof. by elim: cs => [|c cs IH] //=. Qed.

Theorem radcan_eq_refined (F : numFieldType) (r : posroot F) (env : seq F)
    e1 e2 cs rcs :
  radcan_check e1 e2 = Some cs -> refine cs = rcs ->
  all_rconds F (proot r) env rcs -> rinterp r env e1 = rinterp r env e2.
Proof.
move=> H Hr Hc; apply: (radcan_eq_cond H); apply: all_conds_bridge_back.
by apply: refine_sound; rewrite Hr.
Qed.

Theorem radcan_eq_refined0 (F : numFieldType) (env : seq F) e1 e2 cs rcs :
  no_root e1 -> no_root e2 -> radcan_check e1 e2 = Some cs -> refine cs = rcs ->
  all_rconds F (fun _ _ => 0) env rcs -> rinterp0 env e1 = rinterp0 env e2.
Proof.
move=> n1 n2 H Hr Hc; apply: (radcan_eq_cond0 n1 n2 H).
by apply: refine_sound; rewrite Hr.
Qed.
