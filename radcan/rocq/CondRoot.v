(******************************************************************************)
(* CondRoot: roots of expressions, with side conditions.                      *)
(*   nf_rootE m hs bs == root of a radicand split over the basis bs; MOdd:    *)
(*                      proot n (- a) = - proot n a for odd n; MNeg:          *)
(*                      proot n (- a) = proot n a * omega_n; MRealA: even     *)
(*                      roots of even powers give |B| = proot 2 (B ^+ 2)      *)
(*   nf_inv_m m e0 p  == inverse, the omega atoms of a single term inverted   *)
(*                      directly in mode MNeg                                 *)
(*   nf_rootE_sound, nf_inv_m_sound == their soundness                        *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt ZArith Lia.
From Stdlib Require Import QArith_base Qreduction.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts Syntax Backend Mono Factor NF.
From Radcan Require Import Inverse Poly Ratio RealRoot.
From Radcan Require Import CondSimp.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module CondRootF (Import N : NUM).

Include CondSimpF N.

(* Roots of expressions *)

(* proot n c, c a positive rational *)
Definition num_root (n : positive) (c : coef) : option (nf * seq cond) :=
  let q := c_to_Q c in
  if Qnum q is Zpos a then
    let: (u, cs) := nf_inv (RRoot n (Qden q)) (nf_root n (Qden q)) in
    Some (nf_mul (nf_root n a) u, cs)
  else None.

Definition root_atom (n : positive) (e : rexpr) : nf :=
  [:: (c_one, ([:: (ARoot n e, 1%N)], [::]))].

Definition nf_prod (l : seq (nf * nat)) : nf :=
  foldr (fun bk acc => nf_mul (nf_pow bk.1 bk.2) acc) nf_one l.

Definition trivial_dec (rem : nf) (l : seq (nf * nat)) : bool :=
  match l with
  | [:: (_, 1%N)] => if const_of rem is Some c then c_eqb c c_one else false
  | _ => false
  end.

(* proot n (c * prod B ^+ k) split over the factors (needs 0 <= B) *)
Definition root_prod (n : positive) (c : coef) (l : seq (nf * nat))
  : option (nf * seq cond) :=
  if num_root n c is Some (q, cs) then
    Some (nf_mul q (nf_prod (map (fun bk => (root_atom n (nf_to_rexpr bk.1),
                                            bk.2)) l)),
          cs ++ map (fun bk => CGe0 (nf_to_rexpr bk.1)) l)
  else None.

(* the same, but proot n (1 * B) stays the atom proot n B, no condition *)
Definition root_split (n : positive) (c : coef) (l : seq (nf * nat))
  : option (nf * seq cond) :=
  if l is [:: (b, 1%N)] then
    if c_eqb c c_one then Some (root_atom n (nf_to_rexpr b), [::])
    else root_prod n c l
  else root_prod n c l.

(* mode MReal, odd n: proot n (c * prod B ^+ k) split without condition *)
Definition root_prod_m (m : rmode) (n : positive) (c : coef)
  (l : seq (nf * nat)) : option (nf * seq cond) :=
  if real_mode m && odd (Pos.to_nat n) then
    if num_root n c is Some (q, cs) then
      Some (nf_mul q (nf_prod (map (fun bk => (root_atom n (nf_to_rexpr bk.1),
                                              bk.2)) l)), cs)
    else None
  else root_prod n c l.

Definition root_split_m (m : rmode) (n : positive) (c : coef)
  (l : seq (nf * nat)) : option (nf * seq cond) :=
  if l is [:: (b, 1%N)] then
    if c_eqb c c_one then Some (root_atom n (nf_to_rexpr b), [::])
    else root_prod_m m n c l
  else root_prod_m m n c l.

(* mode MRealA: |B| is the atom proot 2 (B ^+ 2); under an even root a     *)
(* factor B ^+ k with k even is read as |B| ^+ k (no condition)             *)
Definition abs_nf (b : nf) : nf := root_atom 2 (RPow (nf_to_rexpr b) 2).

Definition absify (m : rmode) (n : positive) (l : seq (nf * nat)) :
  seq (nf * nat) :=
  if abs_mode m && ~~ odd (Pos.to_nat n) then
    map (fun bk => if odd bk.2 then bk else (abs_nf bk.1, bk.2)) l
  else l.

(* c * prod B^k with c < 0 becomes (-c) * (-B1)^k1 * prod B^k, B1 the first
   factor with an odd exponent such that P B1 *)
Fixpoint flip_odd_gen (P : nf -> bool) (l : seq (nf * nat)) :
  option (seq (nf * nat)) :=
  match l with
  | [::] => None
  | (b, k) :: l' =>
    if odd k && P b then Some ((nf_opp b, k) :: l')
    else if flip_odd_gen P l' is Some l'' then Some ((b, k) :: l'') else None
  end.

(* a basis element B with -B in the hints hs is flipped first *)
Definition flip_odd (hs : seq nf) (l : seq (nf * nat)) :
  option (seq (nf * nat)) :=
  if flip_odd_gen (fun b => has (fun h => nf_eqb h (nf_opp b)) hs) l
    is Some l' then Some l'
  else flip_odd_gen (fun _ => true) l.

Definition omega_nf (n : positive) : nf := root_atom n omega_c.

(* proot n e0, p the normal form of e0 *)
Definition nf_rootE (m : rmode) (hs : seq nf) (bs : seq nf) (n : positive)
  (e0 : rexpr) (p : nf) : nf * seq cond :=
  let giveup := (root_atom n (if nf_wf p then nf_to_rexpr p else e0), [::]) in
  let oddn := odd_mode m && odd (Pos.to_nat n) in
  if p is [::] then ([::], [::]) else
  if const_of p is Some c then
    (if num_root n c is Some res then res else
     if oddn then
       (if num_root n (c_opp c) is Some (q, cs) then (nf_opp q, cs)
        else giveup)
     else if neg_mode m then
       (if num_root n (c_opp c) is Some (q, cs) then (nf_mul q (omega_nf n), cs)
        else giveup)
     else giveup) else
  let: (rem, l) := decompose bs p in
  if nilp l then giveup else
  if const_of rem is Some c then
    if nf_eqb p (nf_mul rem (nf_prod l)) && all (fun bk => nf_wf bk.1) l then
      if c_neg c then
        if oddn then
          (if root_split_m m n (c_opp c) l is Some (q, cs) then (nf_opp q, cs)
           else giveup)
        else if (if negw_mode m then None else flip_odd hs l) is Some l' then
          (if root_split_m m n (c_opp c) (absify m n l') is Some res then res
           else giveup)
        else if neg_mode m then
          (if root_prod n (c_opp c) l is Some (q, cs)
           then (nf_mul q (omega_nf n), cs) else giveup)
        else giveup
      else if trivial_dec rem l then giveup
      else if root_prod_m m n c (absify m n l) is Some res then res
      else giveup
    else giveup
  else giveup.

(* mode MNeg: the omega atoms of a single term are inverted directly,
   omega_n ^- k = (-1) ^+ k * omega_n ^+ (k * (n - 1)) *)
Fixpoint vsplit_omega (v : vmono) : seq (positive * nat) * vmono :=
  match v with
  | [::] => ([::], [::])
  | (a, k) :: v' =>
    let: (o, w) := vsplit_omega v' in
    if a is ARoot n e then
      if is_omega e then ((n, k) :: o, w) else (o, (a, k) :: w)
    else (o, (a, k) :: w)
  end.

Definition omega_inv (o : seq (positive * nat)) : nf :=
  foldr (fun nk acc =>
           nf_mul (nf_mul (nf_pow (nf_opp nf_one) nk.2)
                          [:: (c_one, (vsingle (ARoot nk.1 omega_c)
                                         (nk.2 * (Pos.to_nat nk.1).-1),
                                       [::]))]) acc)
        nf_one o.

Definition nf_inv_m (m : rmode) (e0 : rexpr) (p : nf) : nf * seq cond :=
  if neg_mode m then
    if p is [:: (c, (v, mm))] then
      let: (o, w) := vsplit_omega v in
      if o is [::] then nf_inv e0 p else
      let d := [:: (c, (w, mm))] in
      if nf_wf d then
        let: (q, cs) := nf_inv (nf_to_rexpr d) d in (nf_mul q (omega_inv o), cs)
      else nf_inv e0 p
    else nf_inv e0 p
  else nf_inv e0 p.

Local Open Scope ring_scope.

Section CondRootSound.

Variable F : numFieldType.
Variable r : posroot F.
Variable env : seq F.
(* odd mode: only used with an oddroot, neg mode: only with a negroot *)
Variable mo : rmode.
Hypothesis Ho : odd_mode mo -> oddroot r.
Hypothesis Hng : neg_mode mo -> negroot r.
Hypothesis Hrl : real_mode mo -> realroot r.

Local Notation fct_interp := (fct_interp r).
Local Notation mono_interp := (mono_interp r).
Local Notation atom_interp := (atom_interp r env).
Local Notation vmono_interp := (vmono_interp r env).
Local Notation key_interp := (key_interp r env).
Local Notation holds := (holds r env).
Local Notation nf_interp := (nf_interp r env).

Local Notation cond_interp := (cond_interp r env).
Local Notation all_conds := (all_conds r env).

Local Arguments nf_mul : simpl never.
Local Arguments nf_add : simpl never.
Local Arguments nf_pow : simpl never.
Local Arguments nf_opp : simpl never.

Lemma const_of_sound p c : const_of p = Some c -> nf_interp p = C2F c.
Proof.
case: p => [[<-]|[c' [[|??] [|??]]] [|??]] //=.
  by rewrite nf_interp_nil C2F_c_zero.
move=> [<-]; rewrite nf_interp_cons nf_interp_nil /key_interp /=.
by rewrite vmono_interp_nil mono_interp_nil !mulr1 addr0.
Qed.

Lemma num_root_sound n c res : num_root n c = Some res -> holds res.2 ->
  0 <= C2F (F:=F) c /\ nf_interp res.1 = proot r (Pos.to_nat n) (C2F c).
Proof.
have N0 : (0 < Pos.to_nat n)%N by apply/ssrnat.ltP; exact: Pos2Nat.is_pos.
rewrite /num_root /C2F; case: (c_to_Q c) => [[|a|a] d] //=.
have := @nf_inv_sound F r env (RRoot n d) (nf_root n d)
  (esym (nf_root_sound r env n d)).
case: nf_inv => u cs /= Hu [<-] /= /Hu {}Hu.
have d0 : 0 <= (pos2F F d)^-1 by rewrite invr_ge0 pos2F_ge0.
split; first by rewrite /Q2F /= divr_ge0 ?pos2F_ge0.
rewrite nf_mul_sound Hu !nf_root_sound /Q2F /= prootM ?pos2F_ge0 //.
by rewrite prootV ?pos2F_ge0.
Qed.

Lemma nf_prod_sound l :
  nf_interp (nf_prod l) = \prod_(bk <- l) nf_interp bk.1 ^+ bk.2.
Proof.
elim: l => [|bk l IH] /=; first by rewrite big_nil nf_one_sound.
by rewrite big_cons nf_mul_sound nf_pow_sound IH.
Qed.

Lemma proot_prod n c l : (0 < n)%N -> 0 <= c ->
  (forall bk, List.In bk l -> 0 <= nf_interp bk.1) ->
  proot r n (c * \prod_(bk <- l) nf_interp bk.1 ^+ bk.2) =
  proot r n c * \prod_(bk <- l) proot r n (nf_interp bk.1) ^+ bk.2.
Proof.
move=> n0 c0; elim: l c c0 => [|bk l IH] c c0 Hl.
  by rewrite !big_nil !mulr1.
have b0 : 0 <= nf_interp bk.1 by apply: Hl; left.
have Hl' : forall bk', List.In bk' l -> 0 <= nf_interp bk'.1.
  by move=> bk' H; apply: Hl; right.
rewrite !big_cons mulrA (mulrA c) IH ?mulr_ge0 ?exprn_ge0 //.
by rewrite prootM ?exprn_ge0 // prootX.
Qed.

Lemma all_In (T : Type) (P : pred T) l x : all P l -> List.In x l -> P x.
Proof. by elim: l => [|y l IH] //= /andP[Py Pl] [<-|/IH]; [|apply]. Qed.

Lemma root_atoms_prod n l : (forall bk, List.In bk l -> nf_wf bk.1) ->
  \prod_(bk <- l) nf_interp (root_atom n (nf_to_rexpr bk.1)) ^+ bk.2 =
  \prod_(bk <- l) proot r (Pos.to_nat n) (nf_interp bk.1) ^+ bk.2.
Proof.
elim: l => [|bk l IH] Hw; first by rewrite !big_nil.
rewrite !big_cons IH; last by move=> bk' H; apply: Hw; right.
by rewrite /root_atom nf_atom1 /= nf_to_rexpr_sound //; apply: Hw; left.
Qed.

Lemma root_prod_sound n c l res : root_prod n c l = Some res -> holds res.2 ->
  all (fun bk => nf_wf bk.1) l ->
  nf_interp res.1 =
  proot r (Pos.to_nat n) (C2F c * \prod_(bk <- l) nf_interp bk.1 ^+ bk.2).
Proof.
have N0 : (0 < Pos.to_nat n)%N by apply/ssrnat.ltP; exact: Pos2Nat.is_pos.
rewrite /root_prod; case En : (num_root n c) => [[q cs]|] // [<-] /=.
case/holds_cat => /(num_root_sound En) [c0 Hq] Hl Hwf.
have Hw : forall bk, List.In bk l -> nf_wf bk.1 by move=> bk; apply: all_In Hwf.
have Hb : forall bk, List.In bk l -> 0 <= nf_interp bk.1.
  move=> bk Hbk; have := Hl (CGe0 (nf_to_rexpr bk.1)).
  rewrite /= nf_to_rexpr_sound ?Hw //; apply.
  by apply/List.in_map_iff; exists bk.
rewrite nf_mul_sound Hq proot_prod // nf_prod_sound big_map.
by rewrite root_atoms_prod.
Qed.

Lemma root_split_sound n c l res : root_split n c l = Some res -> holds res.2 ->
  all (fun bk => nf_wf bk.1) l ->
  nf_interp res.1 =
  proot r (Pos.to_nat n) (C2F c * \prod_(bk <- l) nf_interp bk.1 ^+ bk.2).
Proof.
rewrite /root_split.
case: l => [|[b [|[|k]]] [|bk l]]; try exact: root_prod_sound.
case: ifP => [/(@c_eqbP F _ _) Hc [<-] _ /andP[wb _]|_]; last first.
  exact: root_prod_sound.
rewrite /root_atom nf_atom1 /= nf_to_rexpr_sound // Hc C2F_c_one mul1r.
by rewrite big_seq1 expr1.
Qed.

Lemma flip_odd_gen_sound P l l' : flip_odd_gen P l = Some l' ->
  \prod_(bk <- l') nf_interp bk.1 ^+ bk.2 =
    - \prod_(bk <- l) nf_interp bk.1 ^+ bk.2 /\
  (all (fun bk => nf_wf bk.1) l -> all (fun bk => nf_wf bk.1) l').
Proof.
elim: l l' => [|[b k] l IH] l' //=.
case: ifP => [/andP[Ok _] [<-]|_].
  rewrite !big_cons /= nf_opp_sound exprNn -signr_odd Ok expr1 mulN1r mulNr.
  split=> // /andP[wb ->]; rewrite andbT.
  by move: wb; rewrite /nf_wf /nf_opp all_map.
case E : (flip_odd_gen P l) => [l''|] // [<-].
have [H1 H2] := IH _ E.
rewrite !big_cons H1 mulrN; split=> //=.
by case/andP => -> /H2.
Qed.

Lemma flip_odd_sound hs l l' : flip_odd hs l = Some l' ->
  \prod_(bk <- l') nf_interp bk.1 ^+ bk.2 =
    - \prod_(bk <- l) nf_interp bk.1 ^+ bk.2 /\
  (all (fun bk => nf_wf bk.1) l -> all (fun bk => nf_wf bk.1) l').
Proof.
rewrite /flip_odd; case E : flip_odd_gen => [l1|]; last first.
  exact: flip_odd_gen_sound.
by move=> [<-]; apply: flip_odd_gen_sound E.
Qed.

Lemma root_prod_ge0 n c l res : root_prod n c l = Some res -> holds res.2 ->
  all (fun bk => nf_wf bk.1) l ->
  0 <= C2F c * \prod_(bk <- l) nf_interp bk.1 ^+ bk.2.
Proof.
rewrite /root_prod; case En : (num_root n c) => [[q cs]|] // [<-] /=.
case/holds_cat => /(num_root_sound En) [c0 _] Hl Hwf.
rewrite mulr_ge0 //; elim: l Hl Hwf {En} => [|bk l IH] Hl Hwf.
  by rewrite big_nil.
case/andP: Hwf => wb Hwf.
rewrite big_cons mulr_ge0 ?exprn_ge0 //; last first.
  by apply: IH => // c' Hc'; apply: Hl; right.
have := Hl (CGe0 (nf_to_rexpr bk.1)); rewrite /= nf_to_rexpr_sound //.
by apply; left.
Qed.

Lemma proot_prod_odd (rl : realroot r) N (l : seq (nf * nat)) : odd N ->
  proot r N (\prod_(bk <- l) nf_interp bk.1 ^+ bk.2) =
  \prod_(bk <- l) proot r N (nf_interp bk.1) ^+ bk.2.
Proof.
move=> ON; have N0 : (0 < N)%N by case: N ON.
elim: l => [|bk l IH]; first by rewrite !big_nil proot_1.
by rewrite !big_cons (proot_oddM rl) // (proot_oddX rl) // IH.
Qed.

Lemma root_prod_m_sound n c l res : root_prod_m mo n c l = Some res ->
  holds res.2 -> all (fun bk => nf_wf bk.1) l ->
  nf_interp res.1 =
  proot r (Pos.to_nat n) (C2F c * \prod_(bk <- l) nf_interp bk.1 ^+ bk.2).
Proof.
rewrite /root_prod_m; case: ifP => [/andP[Hm On]|_]; last first.
  exact: root_prod_sound.
case En : (num_root n c) => [[q cs]|] // [<-] /= /(num_root_sound En) [c0 Hq].
move=> Hwf.
have Hw : forall bk, List.In bk l -> nf_wf bk.1 by move=> bk; apply: all_In Hwf.
rewrite nf_mul_sound Hq nf_prod_sound big_map root_atoms_prod //.
by rewrite (proot_oddM (Hrl Hm)) // (proot_prod_odd (Hrl Hm)).
Qed.

Lemma root_split_m_sound n c l res : root_split_m mo n c l = Some res ->
  holds res.2 -> all (fun bk => nf_wf bk.1) l ->
  nf_interp res.1 =
  proot r (Pos.to_nat n) (C2F c * \prod_(bk <- l) nf_interp bk.1 ^+ bk.2).
Proof.
rewrite /root_split_m.
case: l => [|[b [|[|k]]] [|bk l]]; try exact: root_prod_m_sound.
case: ifP => [/(@c_eqbP F _ _) Hc [<-] _ /andP[wb _]|_]; last first.
  exact: root_prod_m_sound.
rewrite /root_atom nf_atom1 /= nf_to_rexpr_sound // Hc C2F_c_one mul1r.
by rewrite big_seq1 expr1.
Qed.

Lemma absify_sound n l : all (fun bk => nf_wf bk.1) l ->
  \prod_(bk <- absify mo n l) nf_interp bk.1 ^+ bk.2 =
    \prod_(bk <- l) nf_interp bk.1 ^+ bk.2 /\
  all (fun bk => nf_wf bk.1) (absify mo n l).
Proof.
rewrite /absify; case: ifP => [/andP[Hm _]|_] Hwf //; split; last first.
  elim: (l) Hwf => //= -[b k] l' IH /andP[wb /IH ->].
  by case: ifP; rewrite /= ?wb.
have Hr : real_mode mo by case: (mo) Hm.
elim: l Hwf => [|[b k] l IH] /=; first by rewrite !big_nil.
case/andP => /= wb /IH {}IH; rewrite !big_cons IH; congr (_ * _).
case: ifP => //= Ek.
rewrite /abs_nf /root_atom nf_atom1 /= nf_to_rexpr_sound //.
rewrite (proot_sqr (Hrl Hr)) -(odd_double_half k) Ek add0n.
by rewrite -mul2n !exprM real_normK // (realroot_real (Hrl Hr)).
Qed.

Lemma nf_rootE_sound hs bs n e0 p : rinterp r env e0 = nf_interp p ->
  holds (nf_rootE mo hs bs n e0 p).2 ->
  nf_interp (nf_rootE mo hs bs n e0 p).1 = proot r (Pos.to_nat n) (nf_interp p).
Proof.
move=> He.
have N0 : (0 < Pos.to_nat n)%N by apply/ssrnat.ltP; exact: Pos2Nat.is_pos.
have Hg : nf_interp (root_atom n (if nf_wf p then nf_to_rexpr p else e0)) =
          proot r (Pos.to_nat n) (nf_interp p).
  rewrite /root_atom nf_atom1 /=.
  by case: ifP => [/nf_to_rexpr_sound -> | _]; rewrite ?He.
have HN : odd_mode mo && odd (Pos.to_nat n) -> forall a,
    proot r (Pos.to_nat n) a = - proot r (Pos.to_nat n) (- a).
  by case/andP => /Ho Hor On a; rewrite (prootN Hor) // opprK.
have HW : neg_mode mo -> forall a, 0 <= a ->
    proot r (Pos.to_nat n) (- a) =
    proot r (Pos.to_nat n) a * nf_interp (omega_nf n).
  move=> /Hng w a a0.
  by rewrite /omega_nf /root_atom nf_atom1 /= pos2F1 (prootN1 w N0 a0).
rewrite /nf_rootE; case: p He Hg => [|t p'] He Hg.
  by rewrite /= nf_interp_nil proot_0.
set p := t :: p'.
case Ec : (const_of p) => [c|].
  case En : (num_root n c) => [res|].
    by move=> /(num_root_sound En) [_ ->]; rewrite (const_of_sound Ec).
  case: ifP => [On|_].
    case En' : (num_root n (c_opp c)) => [[q cs]|] //=.
    move=> /(num_root_sound En') /= [_ Hq].
    by rewrite nf_opp_sound Hq (const_of_sound Ec) [RHS](HN On) C2F_c_opp.
  case: ifP => [Hm|_ //].
  case En' : (num_root n (c_opp c)) => [[q cs]|] //=.
  move=> /(num_root_sound En') /= [c0 Hq].
  by rewrite nf_mul_sound Hq -(HW Hm _ c0) (const_of_sound Ec) C2F_c_opp opprK.
case: (decompose bs p) => rem l.
case: ifP => _ //.
case Er : (const_of rem) => [c|] //.
case: ifP => [/andP[/nf_eqb_eq Hp Hwf]|_] //.
have Hpc : nf_interp p = C2F c * \prod_(bk <- l) nf_interp bk.1 ^+ bk.2.
  by rewrite Hp nf_mul_sound (const_of_sound Er) nf_prod_sound.
case: ifP => _.
  case: ifP => [On|_].
    case Es : (root_split_m mo n (c_opp c) l) => [[q cs]|] //= Hh.
    rewrite nf_opp_sound (root_split_m_sound Es Hh Hwf) Hpc [RHS](HN On).
    by rewrite C2F_c_opp mulNr.
  case Ef : (if negw_mode mo then None else flip_odd hs l) => [l'|].
    have Ef' : flip_odd hs l = Some l' by move: Ef; case: ifP.
    have [Hl' Hw'] := flip_odd_sound Ef'.
    have [Ha Hwa] := absify_sound n (Hw' Hwf).
    case Es : (root_split_m mo n (c_opp c) (absify mo n l')) => [res|] // Hh.
    rewrite (root_split_m_sound Es Hh Hwa) Ha Hpc Hl' C2F_c_opp.
    by rewrite mulrNN.
  case: ifP => [Hm|_ //].
  case Es : (root_prod n (c_opp c) l) => [[q cs]|] //= Hh.
  rewrite nf_mul_sound (root_prod_sound Es Hh Hwf).
  rewrite -HW ?(root_prod_ge0 Es Hh Hwf) //.
  by rewrite Hpc C2F_c_opp mulNr opprK.
case: ifP => _ //.
have [Ha Hwa] := absify_sound n Hwf.
case Es : (root_prod_m mo n c (absify mo n l)) => [res|] // Hh.
by rewrite (root_prod_m_sound Es Hh Hwa) Ha Hpc.
Qed.

(* inverses of omega atoms (mode MNeg) *)

Lemma vsplit_omega_sound v :
  vmono_interp v = vmono_interp (vsplit_omega v).2 *
    \prod_(nk <- (vsplit_omega v).1) proot r (Pos.to_nat nk.1) (-1) ^+ nk.2.
Proof.
elim: v => [|[a k] v IH] /=; first by rewrite vmono_interp_nil big_nil mulr1.
case: (vsplit_omega v) IH => o w /= IH.
have Hd : vmono_interp ((a, k) :: v) = vmono_interp ((a, k) :: w) *
    \prod_(nk <- o) proot r (Pos.to_nat nk.1) (-1) ^+ nk.2.
  by rewrite !vmono_interp_cons IH mulrA.
case: a Hd => [i|e|n e] Hd //; case: ifP => [/is_omegaP -> |_] //.
by rewrite vmono_interp_cons IH big_cons /= pos2F1 mulrCA.
Qed.

Lemma omega_inv_sound (w : negroot r) o :
  nf_interp (omega_inv o) =
    (\prod_(nk <- o) proot r (Pos.to_nat nk.1) (-1) ^+ nk.2)^-1.
Proof.
elim: o => [|[n k] o IH] /=; first by rewrite nf_one_sound big_nil invr1.
have N0 : (0 < Pos.to_nat n)%N by apply/ssrnat.ltP; exact: Pos2Nat.is_pos.
rewrite nf_mul_sound IH big_cons invfM /=; congr (_ * _).
rewrite nf_mul_sound nf_pow_sound nf_opp_sound nf_one_sound.
rewrite nf_interp_cons nf_interp_nil addr0 /key_interp /= vsingle_sound /=.
rewrite mono_interp_nil C2F_c_one pos2F1 !mulr1 mul1r.
set x := proot r _ (-1).
have xN : x ^+ Pos.to_nat n = -1 by exact: prootN1K.
have x0 : x != 0.
  apply/eqP => x0; move: xN; rewrite x0 expr0n gtn_eqF // => /eqP.
  by rewrite eq_sym oppr_eq0 oner_eq0.
have Hk : x ^+ (k * (Pos.to_nat n).-1) * x ^+ k = (-1) ^+ k.
  by rewrite -exprD -mulnSr prednK // mulnC exprM xN.
apply: (mulIf (expf_neq0 k x0)); rewrite mulVf ?expf_neq0 // -mulrA Hk.
by rewrite -exprMn mulrNN mulr1 expr1n.
Qed.

Lemma nf_inv_m_sound e0 p :
  rinterp r env e0 = nf_interp p -> holds (nf_inv_m mo e0 p).2 ->
  nf_interp (nf_inv_m mo e0 p).1 = (nf_interp p)^-1.
Proof.
move=> He; rewrite /nf_inv_m; case: ifP => [Hm|_]; last exact: nf_inv_sound He.
have w : negroot r by apply: Hng; case: (mo) Hm.
case: p He => [|[c [v mm]] [|t p]] He;
  [exact: nf_inv_sound He| |exact: nf_inv_sound He].
have := vsplit_omega_sound v; case: (vsplit_omega v) => o vw Hv.
case: o Hv => [|nk o] Hv; first exact: nf_inv_sound He.
case: ifP => [Hwf|_]; last exact: nf_inv_sound He.
have := @nf_inv_sound F r env _ [:: (c, (vw, mm))]
  (nf_to_rexpr_sound r env Hwf).
case: nf_inv => q cs Hq /Hq {}Hq.
rewrite nf_mul_sound Hq (omega_inv_sound w) -invfM.
rewrite !nf_interp_cons !nf_interp_nil !addr0.
by rewrite /key_interp /= Hv /= -!mulrA (mulrC (mono_interp _)).
Qed.

End CondRootSound.

End CondRootF.
