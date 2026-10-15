(******************************************************************************)
(* GaussMode: every square root of a positive integer as a sum of roots of -1 *)
(* (quadratic Gauss sums, GaussSum.v), compared by cyclotomic reduction.      *)
(*   gaussroot w == record of facts on w : negroot r (wn = wroot w n):        *)
(*                  sqrt 2 = w4 - w4 ^+ 3,                                    *)
(*                  sqrt n = sum_(a < n) wn ^+ (2 a^2 mod 2n)     (n = 1 [4]) *)
(*                  sqrt n = sum_(a < n) w2n ^+ ((3n + 4 a^2) mod 4n)         *)
(*                                                                (n = 3 [4]) *)
(*                  (instance rootC_gaussroot C in GaussC.v)                  *)
(*   wgauss r    == the same on proot r n (-1); gaussroot_wgauss              *)
(*   om_pow n k  == omega_n ^+ k as a normal form; om_lcm p == the lcm of the *)
(*                  omega indices of p; gauss2_nf == w4 - w4 ^+ 3 (sqrt 2)    *)
(*   split2 b    == (k, m) with b = 2 ^ k * m, m odd                          *)
(*   gidx b      == the index of the omega atoms of the sum of sqrt b:        *)
(*                  lcm (4 if k odd, else 1) (m if m = 1 [4], else 2m)        *)
(*   gauss_nf b  == sqrt b as a normal form in omega atoms:                   *)
(*                  2 ^ (k / 2) * (w4 - w4 ^+ 3) ^ (k mod 2) * G_m            *)
(*   gs_subst N p == the substitution (trigger rule, N the lcm of the omega   *)
(*                  indices of the goal): in each term, the product B of the  *)
(*                  constant square roots is replaced by gauss_nf B when      *)
(*                  gidx B | N; otherwise each square root sqrt b with        *)
(*                  gidx b | N is replaced by gauss_nf b.  No new omega index *)
(*                  beyond the divisors of N appears: the cyclotomic field of *)
(*                  the goal, hence the size of the reduction, is unchanged.  *)
(*   radcan_check_gauss e1 e2 == the normal forms of modes MNegC, MNegCW,     *)
(*                  substituted by gs_subst, compared by cyc_eqb (Cyclo.v)    *)
(*   radcan_eq_cond_gauss, radcan_eq_refined_gauss == the decision theorems,  *)
(*                  given w : negroot r, cycroot w, cycprim w, gaussroot w    *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts Syntax Radcan Refine.
From Radcan Require Import RealRoot OmegaRoot2 Cyclo.
Import Order.TTheory GRing.Theory Num.Theory ZNum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(* The facts *)

Record gaussroot (F : numFieldType) (r : posroot F) (w : negroot r) : Prop :=
  GaussRoot {
  wgauss2 : proot r 2 2 = wroot w 4 - wroot w 4 ^+ 3;
  wgauss1 : forall n, (n %% 4 = 1)%N ->
    proot r 2 n%:R = \sum_(a < n) wroot w n ^+ ((a * a).*2 %% n.*2);
  wgauss3 : forall n, (n %% 4 = 3)%N ->
    proot r 2 n%:R =
    \sum_(a < n) wroot w n.*2 ^+ ((n * 3 + a * a * 4) %% (n * 4))
}.

Definition wgauss (F : numFieldType) (r : posroot F) : Prop :=
  [/\ proot r 2 2 = proot r 4 (-1) - proot r 4 (-1) ^+ 3,
      forall n, (n %% 4 = 1)%N ->
        proot r 2 n%:R = \sum_(a < n) proot r n (-1) ^+ ((a * a).*2 %% n.*2)
    & forall n, (n %% 4 = 3)%N ->
        proot r 2 n%:R =
        \sum_(a < n) proot r n.*2 (-1) ^+ ((n * 3 + a * a * 4) %% (n * 4))].

(* The substitution on normal forms *)

(* omega_n ^+ k, and the lcm of the omega indices of a normal form *)
Definition om_pow (n : positive) (k : nat) : nf := nf_pow (omega_nf n) k.

Definition om_lcm (p : nf) : nat :=
  foldr (fun t acc =>
           foldr (fun ak acc =>
                    if ak.1 is ARoot n e then
                      if is_omega e then lcmn (Pos.to_nat n) acc else acc
                    else acc) acc t.2.1) 1%N p.

(* sqrt 2 = w4 - w4 ^+ 3 *)
Definition gauss2_nf : nf := nf_add (om_pow 4 1) (nf_opp (om_pow 4 3)).

Fixpoint split2 (p : positive) : nat * positive :=
  if p is xO q then let: (k, m) := split2 q in (k.+1, m) else (0%N, p).

Definition gidx_odd (m : nat) : nat := if (m %% 4 == 1)%N then m else m.*2.

Definition gidx (b : positive) : nat :=
  let: (k, m) := split2 b in
  lcmn (if odd k then 4 else 1) (gidx_odd (Pos.to_nat m)).

Definition gs_sum (n : positive) (f : nat -> nat) (m : nat) : nf :=
  foldr (fun a acc => nf_add (om_pow n (f a)) acc) [::] (iota 0 m).

Definition gauss_odd (m : nat) : nf :=
  if (m %% 4 == 1)%N then
    gs_sum (Pos.of_nat m) (fun a => (a * a).*2 %% m.*2)%N m
  else gs_sum (Pos.of_nat m.*2) (fun a => (m * 3 + a * a * 4) %% (m * 4))%N m.

Definition nf_two : nf := nf_single (c_of_Z (Zpos 2)) ([::], [::]).

Definition gauss_nf (b : positive) : nf :=
  let: (k, m) := split2 b in
  nf_mul (nf_pow nf_two k./2)
    (nf_mul (if odd k then gauss2_nf else nf_one) (gauss_odd (Pos.to_nat m))).

(* b ^ e *)
Definition ppow (b : positive) (e : nat) : positive :=
  iter e (Pos.mul b) 1%positive.

Definition fct_val (f : fct) : positive := ppow f.1.1 f.2.

Definition gtrig (N : nat) (b : positive) : bool := (gidx b %| N)%N.

Definition is_sq (f : fct) : bool := f.1.2 == 2%N.

(* the term t with the factors of P replaced by G (the factors of P) *)
Definition gs_repl (P : pred fct) (G : seq fct -> nf) (t : coef * key) : nf :=
  nf_mul [:: (t.1, (t.2.1, [seq f <- t.2.2 | ~~ P f]))]
    (G [seq f <- t.2.2 | P f]).

Definition gs_all (l : seq fct) : nf :=
  gauss_nf (foldr (fun f acc => Pos.mul (fct_val f) acc) 1%positive l).

Definition gs_each (l : seq fct) : nf :=
  foldr (fun f acc => nf_mul (gauss_nf (fct_val f)) acc) nf_one l.

Definition gs_term (N : nat) (t : coef * key) : nf :=
  let sq := [seq f <- t.2.2 | is_sq f] in
  if nilp sq then [:: t] else
  if gtrig N (foldr (fun f acc => Pos.mul (fct_val f) acc) 1%positive sq)
  then gs_repl is_sq gs_all t
  else
    let P f := is_sq f && gtrig N (fct_val f) in
    if has P t.2.2 then gs_repl P gs_each t else [:: t].

Definition gs_subst (N : nat) (p : nf) : nf :=
  foldr (fun t acc => nf_add (gs_term N t) acc) [::] p.

(* The checkers *)

Definition radcan_check_gauss_bs (rt : bool) (m : rmode) (hs bs : seq nf)
  (e1 e2 : rexpr) : option (seq cond) :=
  let: (p1, p2, cs) := radcan_nfb rt m hs bs e1 e2 in
  let N := lcmn (om_lcm p1) (om_lcm p2) in
  if cyc_eqb (gs_subst N p1) (gs_subst N p2) then Some cs else None.

Definition radcan_check_gauss_m (m : rmode) (e1 e2 : rexpr) :
    option (seq cond) :=
  let cb := const_basis (rconsts m e1 ++ rconsts m e2) in
  let f1 := cb_rw m cb e1 in let f2 := cb_rw m cb e2 in
  let hs := neg_hints [:: f1; f2] in
  let ck rt := radcan_check_gauss_bs rt m hs (mk_basis_n rt m hs [:: f1; f2])
                 f1 f2 in
  if ck false is Some cs then Some cs else ck true.

Definition radcan_check_gauss (e1 e2 : rexpr) : option (seq cond) :=
  if radcan_check_gauss_m MNegC e1 e2 is Some cs then Some cs
  else radcan_check_gauss_m MNegCW e1 e2.

(* Soundness *)

Lemma gaussroot_wgauss (F : numFieldType) (r : posroot F) (w : negroot r) :
  gaussroot w -> wgauss r.
Proof.
case=> h2 h1 h3; split; first by rewrite h2 !(wrootE w).
  move=> n n4; have n0 : (0 < n)%N by case: n n4.
  by rewrite h1 //; apply: eq_bigr => a _; rewrite (wrootE w).
move=> n n4; have n0 : (0 < n.*2)%N by rewrite double_gt0; case: n n4.
by rewrite h3 //; apply: eq_bigr => a _; rewrite (wrootE w).
Qed.

Lemma split2_sound p k m : split2 p = (k, m) ->
  Pos.to_nat p = (2 ^ k * Pos.to_nat m)%N /\ odd (Pos.to_nat m).
Proof.
elim: p k m => [p _|p IH|] k m.
- move=> [<- <-]; rewrite expn0 mul1n; split => //.
  by rewrite Pos2Nat.inj_xI -[(2 * _)%coq_nat]/(2 * _)%N mul2n oddS odd_double.
- rewrite [split2 _]/=; case E : (split2 p) => [k' m'] [<- <-].
  have [{}E O] := IH _ _ E; split => //.
  by rewrite Pos2Nat.inj_xO -[(2 * _)%coq_nat]/(2 * _)%N E expnS mulnA.
by move=> [<- <-].
Qed.

Lemma ppow_sound (F : numFieldType) b e :
  pos2F F (ppow b e) = pos2F F b ^+ e.
Proof.
elim: e => [|e IH]; first by rewrite expr0 pos2F1.
by rewrite /ppow iterS -/(ppow b e) pos2F_mul IH exprS.
Qed.

Lemma odd_mod4 m : odd m -> (m %% 4 != 1)%N -> (m %% 4 = 3)%N.
Proof.
move=> om; have : odd (m %% 4).
  by move: om; rewrite [m in odd m](divn_eq m 4) oddD oddM andbF.
have : (m %% 4 < 4)%N by rewrite ltn_mod.
by case: (m %% 4)%N => [|[|[|[|]]]].
Qed.

Section Sound.

Variables (F : numFieldType) (r : posroot F) (env : seq F).
Hypothesis hg : wgauss r.

Local Notation nf_interp := (nf_interp r env).
Local Notation key_interp := (key_interp r env).
Local Notation mono_interp := (mono_interp r).
Local Notation om n := (proot r n (-1)).

Local Arguments nf_add : simpl never.
Local Arguments nf_mul : simpl never.

Lemma om_pow_sound n k :
  nf_interp (om_pow n k) = proot r (Pos.to_nat n) (-1) ^+ k.
Proof.
rewrite /om_pow nf_pow_sound /omega_nf /root_atom nf_interp_cons nf_interp_nil.
rewrite addr0 C2F_c_one mul1r /key_interp mono_interp_nil mulr1 /=.
by rewrite vmono_interp_cons vmono_interp_nil mulr1 expr1 /= pos2F1.
Qed.

Lemma gs_sum_sound n f m :
  nf_interp (gs_sum n f m) = \sum_(a < m) om (Pos.to_nat n) ^+ f a.
Proof.
rewrite /gs_sum -(big_mkord xpredT (fun a => om (Pos.to_nat n) ^+ f a)).
rewrite /index_iota subn0; elim: (iota 0 m) => [|a s IH] /=.
  by rewrite big_nil nf_interp_nil.
by rewrite big_cons nf_add_sound om_pow_sound IH.
Qed.

Lemma gauss_odd_sound m : odd m ->
  nf_interp (gauss_odd m) = proot r 2 m%:R.
Proof.
case: hg => _ h1 h3 mo; have m0 : (0 < m)%N by case: m mo.
rewrite /gauss_odd; case: eqP => [m4|/eqP m4]; rewrite gs_sum_sound.
  by rewrite Nat2Pos.id ?h1 //; case: m m0 {mo m4}.
have n0 : (m.*2 <> 0)%N by case: m m0 {mo m4}.
by rewrite Nat2Pos.id // h3 //; exact: odd_mod4.
Qed.

Lemma gauss2_nf_sound : nf_interp gauss2_nf = proot r 2 2.
Proof.
case: hg => h2 _ _; rewrite /gauss2_nf nf_add_sound nf_opp_sound.
by rewrite !om_pow_sound expr1 h2.
Qed.

Lemma nf_two_sound : nf_interp nf_two = 2.
Proof.
rewrite /nf_two nf_single_sound C2F_c_of_Z /key_interp /= vmono_interp_nil.
by rewrite mono_interp_nil !mulr1.
Qed.

Lemma gauss_nf_sound b : nf_interp (gauss_nf b) = proot r 2 (pos2F F b).
Proof.
rewrite /gauss_nf; case S2 : (split2 b) => [k m].
have [E O] := split2_sound S2.
rewrite !nf_mul_sound nf_pow_sound nf_two_sound gauss_odd_sound //.
rewrite /pos2F E natrM natrX prootM ?exprn_ge0 ?ler0n // prootX ?ler0n //.
rewrite -[in RHS](odd_double_half k) exprD mulrA; congr (_ * _).
rewrite -[k./2.*2]muln2 mulnC exprM prootK ?ler0n // mulrC; congr (_ * _).
by case: (odd k); rewrite ?nf_one_sound ?gauss2_nf_sound.
Qed.

Lemma fct_val_sound f : is_sq f ->
  fct_interp r f = proot r 2 (pos2F F (fct_val f)).
Proof.
case: f => [[b n] e] /eqP /= ->.
by rewrite ppow_sound prootX ?pos2F_ge0.
Qed.

Lemma gs_all_sound l : all is_sq l -> nf_interp (gs_all l) = mono_interp l.
Proof.
rewrite /gs_all gauss_nf_sound; elim: l => [|f l IH] /=.
  by rewrite pos2F1 proot_1 // mono_interp_nil.
case/andP => Hf /IH {}IH; rewrite pos2F_mul prootM ?pos2F_ge0 //.
by rewrite IH mono_interp_cons fct_val_sound.
Qed.

Lemma gs_each_sound l : all is_sq l -> nf_interp (gs_each l) = mono_interp l.
Proof.
elim: l => [|f l IH] /=; first by rewrite nf_one_sound mono_interp_nil.
case/andP => Hf /IH {}IH; rewrite nf_mul_sound IH gauss_nf_sound.
by rewrite mono_interp_cons fct_val_sound.
Qed.

Lemma mono_interp_split (P : pred fct) m :
  mono_interp m =
  mono_interp [seq f <- m | ~~ P f] * mono_interp [seq f <- m | P f].
Proof. by rewrite /mono_interp !big_filter [LHS](bigID P) /= mulrC. Qed.

Lemma gs_repl_sound (P : pred fct) G t :
  (forall l, all P l -> nf_interp (G l) = mono_interp l) ->
  nf_interp (gs_repl P G t) = C2F t.1 * key_interp t.2.
Proof.
move=> HG; rewrite /gs_repl nf_mul_sound HG ?filter_all //.
rewrite nf_interp_cons nf_interp_nil addr0 /key_interp /=.
by rewrite [mono_interp t.2.2](mono_interp_split P) !mulrA.
Qed.

Lemma gs_term_sound N t : nf_interp (gs_term N t) = C2F t.1 * key_interp t.2.
Proof.
have Ht : nf_interp [:: t] = C2F t.1 * key_interp t.2.
  by rewrite nf_interp_cons nf_interp_nil addr0.
rewrite /gs_term; case: ifP => // _; case: ifP => _.
  by apply: gs_repl_sound => l; exact: gs_all_sound.
case: ifP => // _; apply: gs_repl_sound => l Hl; apply: gs_each_sound.
by apply: sub_all Hl => f /andP[].
Qed.

Lemma gs_subst_sound N p : nf_interp (gs_subst N p) = nf_interp p.
Proof.
elim: p => [|t p IH] //=.
by rewrite nf_add_sound IH gs_term_sound nf_interp_cons.
Qed.

End Sound.

Section CheckSound.

Variables (F : numFieldType) (r : posroot F) (env : seq F).
Hypotheses (hw : windex r) (hp : wprim r) (hg : wgauss r).
Variable m : rmode.
Hypotheses (Hng : neg_mode m -> negroot r) (Hcy : cyc_mode m -> windex r).
Hypothesis Ho : odd_mode m -> oddroot r.
Hypothesis Hrl : real_mode m -> realroot r.

Lemma radcan_check_gauss_bs_sound rt hs bs e1 e2 cs :
  radcan_check_gauss_bs rt m hs bs e1 e2 = Some cs ->
  all_conds r env cs -> rinterp r env e1 = rinterp r env e2.
Proof.
have H1 := @normcr_sound F r env m Ho Hng Hrl Hcy rt hs bs e1.
have H2 := @normcr_sound F r env m Ho Hng Hrl Hcy rt hs bs e2.
set n1 := normcr rt m hs bs e1 in H1 *; set n2 := normcr rt m hs bs e2 in H2 *.
have E : radcan_check_gauss_bs rt m hs bs e1 e2 =
    if cyc_eqb (gs_subst (lcmn (om_lcm n1.1) (om_lcm n2.1)) n1.1)
               (gs_subst (lcmn (om_lcm n1.1) (om_lcm n2.1)) n2.1)
    then Some (cfilter m (cdedup (n1.2 ++ n2.2))) else None.
  clear H1 H2; rewrite /radcan_check_gauss_bs /radcan_nfb -/n1 -/n2.
  by case: n1; case: n2.
rewrite E; case: ifP => // /(cyc_eqb_sound env hw hp) Hp [<-].
move: Hp; rewrite !(gs_subst_sound _ hg) => Hp.
move=> /all_condsP /(cfilter_sound Hrl) /holds_dedup /holds_cat.
by case=> /H1 -> /H2 ->.
Qed.

Lemma radcan_check_gauss_m_sound e1 e2 cs :
  radcan_check_gauss_m m e1 e2 = Some cs ->
  all_conds r env cs -> rinterp r env e1 = rinterp r env e2.
Proof.
rewrite /radcan_check_gauss_m; set cb := const_basis _.
rewrite -(cb_rw_sound env Ho Hng cb e1) -(cb_rw_sound env Ho Hng cb e2).
by case/ocase_some => /radcan_check_gauss_bs_sound.
Qed.

End CheckSound.

(* The decision theorems *)

Theorem radcan_eq_cond_gauss (F : numFieldType) (r : posroot F)
    (w : negroot r) (cy : cycroot w) (cp : cycprim w) (gs : gaussroot w)
    (env : seq F) e1 e2 cs :
  radcan_check_gauss e1 e2 = Some cs -> all_conds r env cs ->
  rinterp r env e1 = rinterp r env e2.
Proof.
have hw := cycroot_windex cy; have hp := cycprim_wprim cp.
have hg := gaussroot_wgauss gs.
rewrite /radcan_check_gauss.
by case/ocase_some => H; apply: (radcan_check_gauss_m_sound hw hp hg _ _ _ _ H).
Qed.

Theorem radcan_eq_refined_gauss (F : numFieldType) (r : posroot F)
    (w : negroot r) (cy : cycroot w) (cp : cycprim w) (gs : gaussroot w)
    (env : seq F) e1 e2 cs rcs :
  radcan_check_gauss e1 e2 = Some cs -> refine cs = rcs ->
  all_rconds F (proot r) env rcs -> rinterp r env e1 = rinterp r env e2.
Proof.
move=> H Hr Hc; apply: (radcan_eq_cond_gauss cy cp gs H).
by apply: all_conds_bridge_back; apply: refine_sound; rewrite Hr.
Qed.
