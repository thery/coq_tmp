(******************************************************************************)
(* Inverse: inversion of normal forms, in module InverseF N.                  *)
(*   nf_inv_cand d   == candidate inverse by Gauss-Jordan elimination over Q  *)
(*                      on the basis of root monomials (at most max_dim)      *)
(*   nf_inv_num d    == the candidate, checked by multiplication              *)
(*   nf_atom_inv e d == d^-1 as an inverse atom AInv: the atom is the         *)
(*                      primitive part of d with a positive leading           *)
(*                      coefficient (nf_prim, checked), so that 2 x + 2 and   *)
(*                      x + 1 give the same atom                              *)
(*   nf_atom_inv_m   == a root monomial common to all terms is inverted apart *)
(*   nf_inv e d      == the inverse of d, the normal form of e, with the      *)
(*                      side conditions it needs                              *)
(*   nf_inv0 d       == root-free variant                                     *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt ZArith Lia.
From Stdlib Require Import QArith_base Qreduction.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts Syntax Backend Mono Factor NF.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module InverseF (Import N : NUM).

Include NFF N.

(* Candidate inverse by linear algebra over Q *)

Definition novar (p : nf) : bool := all (fun t => nilp t.2.1) p.

Fixpoint ins_base (b : positive) (n : nat) (l : seq (positive * nat)) :=
  match l with
  | [::] => [:: (b, n)]
  | (b', n') :: l' =>
    if p_eqb b b' then (b', lcmn n n') :: l' else (b', n') :: ins_base b n l'
  end.

(* each base with the lcm of its indices *)
Definition nf_bases (p : nf) : seq (positive * nat) :=
  foldr (fun t acc => foldr (fun f acc => ins_base f.1.1 f.1.2 acc) acc t.2.2)
        [::] p.

(* the monomials prod_b b^(e_b/L_b), 0 <= e_b < L_b *)
Definition nf_basis (bl : seq (positive * nat)) : seq mono :=
  foldr (fun bn acc =>
           flatten (map (fun e =>
                          map (fun m => (mono_mul (fct_norm bn.1 bn.2 e).2 m).2)
                              acc)
                        (iota 0 bn.2)))
        [:: [::]] bl.

Fixpoint coef_of (m : mono) (p : nf) : coef :=
  match p with
  | [::] => c_zero
  | t :: p' =>
    if nilp t.2.1 && cmp_eqb (mono_cmp t.2.2 m) then t.1 else coef_of m p'
  end.

Definition row := seq coef.

Fixpoint row_sub (rw p : row) (a : coef) : row :=
  match rw, p with
  | x :: rw', y :: p' => c_sub x (c_mul a y) :: row_sub rw' p' a
  | _, _ => rw
  end.

Fixpoint find_pivot (c : nat) (todo : seq row) : option (row * seq row) :=
  match todo with
  | [::] => None
  | rw :: t =>
    if c_is0 (nth c_zero rw c) then
      if find_pivot c t is Some (p, t') then Some (p, rw :: t') else None
    else Some (rw, t)
  end.

(* Gauss-Jordan elimination on an augmented matrix *)
Fixpoint gauss (c fuel : nat) (done todo : seq row) : option (seq row) :=
  match fuel with
  | O => Some done
  | S f =>
    if find_pivot c todo is Some (p, t) then
      let pv := c_inv (nth c_zero p c) in
      let p' := map (fun x => c_mul x pv) p in
      let el := fun rw => row_sub rw p' (nth c_zero rw c) in
      gauss c.+1 f (rcons (map el done) p') (map el t)
    else None
  end.

Definition max_dim := 64%N.

Definition nf_inv_cand (d : nf) : option nf :=
  let bl := nf_bases d in
  if (foldr (fun bn a => bn.2 * a) 1 bl > max_dim)%N then None else
  let B := nf_basis bl in
  let cols := map (fun b => nf_mul d [:: (c_one, ([::], b))]) B in
  let rows :=
    map (fun bi => rcons (map (coef_of bi) cols) (coef_of bi nf_one)) B in
  if gauss 0 (size B) [::] rows is Some sol then
    Some (foldr (fun bv acc =>
                   nf_add (nf_single (last c_zero bv.2) ([::], bv.1)) acc)
                [::] (zip B sol))
  else None.

(* Inverse atoms: d = c * d', d' primitive with a positive leading
   coefficient (checked), d^-1 = c^-1 * d'^-1 *)

Definition vdeg (v : vmono) : nat := sumn (map snd v).

Fixpoint mlex (v1 v2 : vmono) : comparison :=
  match v1, v2 with
  | [::], [::] => Eq
  | [::], _ => Lt
  | _, [::] => Gt
  | (a1, k1) :: v1', (a2, k2) :: v2' =>
    match atom_cmp a1 a2 with
    | Eq => lex (Nat.compare k1 k2) (mlex v1' v2')
    | Lt => Gt
    | Gt => Lt
    end
  end.

Definition mcmp (v1 v2 : vmono) : comparison :=
  lex (Nat.compare (vdeg v1) (vdeg v2)) (mlex v1 v2).

Definition lead (p : nf) : option (coef * vmono) :=
  foldr (fun t acc => if acc is Some (_, v) then
                        (if mcmp t.2.1 v is Gt then Some (t.1, t.2.1) else acc)
                      else Some (t.1, t.2.1)) None p.

Definition primitive (p : nf) : nf :=
  let g := foldr (fun t a => Z.gcd (Qnum (c_to_Q t.1)) a) Z0 p in
  let l := foldr (fun t a => Z.lcm (Zpos (Qden (c_to_Q t.1))) a) Z1 p in
  if Z.eqb g Z0 then p
  else map (fun t => (c_mul t.1 (c_div (c_of_Z l) (c_of_Z g)), t.2)) p.

Definition c_neg (c : coef) : bool :=
  if Qnum (c_to_Q c) is Zneg _ then true else false.

(* B and -B give the same atom: the sign goes to the coefficient *)
Definition normsign (p : nf) : nf :=
  if lead p is Some (c, _) then (if c_neg c then nf_opp p else p) else p.

Definition nf_scale (c : coef) (p : nf) : nf :=
  map (fun t => (c_mul c t.1, t.2)) p.

(* d = c * d' (to be checked) *)
Definition nf_prim (d : nf) : coef * nf :=
  let d' := normsign (primitive d) in
  if d is t :: _ then
    (if d' is t' :: _ then (c_div t.1 t'.1, d') else (c_one, d))
  else (c_one, d).

Definition prim_ok (d : nf) (c : coef) (d' : nf) : bool :=
  ~~ c_is0 c && nf_eqb d (nf_scale c d').

Definition nf_atom_inv (e0 : rexpr) (d : nf) : nf :=
  let: (c, d') := nf_prim d in
  if prim_ok d c d' && nf_wf d' then
    nf_scale (c_inv c) (atom_nf (AInv (nf_to_rexpr d')))
  else
  let e := if nf_wf d then nf_to_rexpr d else e0 in
  [:: (c_one, ([:: (AInv e, 1%N)], [::]))].

Definition atom_inv_nf (a : atom) : nf * seq cond :=
  match a with
  | AVar i => ([:: (c_one, ([:: (AInv (RVar i), 1%N)], [::]))], [::])
  | AInv e => (pnorm e, [::])
  | ARoot n e =>
    ([:: (c_one, (vmono_mul (vsingle (ARoot n e) (Pos.to_nat n).-1)
                            [:: (AInv e, 1%N)], [::]))],
     [:: CGe0 e])
  end.

Definition vinv (v : vmono) : nf * seq cond :=
  foldr (fun ak acc => let: (q, cs) := atom_inv_nf ak.1 in
                       (nf_mul (nf_pow q ak.2) acc.1, cs ++ acc.2))
        (nf_one, [::]) v.

Definition nf_inv_num (d : nf) : option nf :=
  if nf_inv_cand d is Some u then
    if nf_eqb (nf_mul d u) nf_one then Some u else None
  else None.

(* d = m * d'' (checked), m a root monomial shared by all the terms of d,
   d^-1 = m^-1 * d''^-1, m inverted by linear algebra *)
Definition nf_mono_split (d : nf) : option (nf * nf) :=
  if d is t :: _ then
    let m := t.2.2 in
    if ~~ nilp m && all (fun t' => cmp_eqb (mono_cmp t'.2.2 m)) d then
      Some ([:: (c_one, ([::], m))], map (fun t' => (t'.1, (t'.2.1, [::]))) d)
    else None
  else None.

Definition nf_atom_inv_m (e0 : rexpr) (d : nf) : nf :=
  if nf_mono_split d is Some (M, d'') then
    if nf_inv_num M is Some u then
      if nf_eqb d (nf_mul M d'') && nf_wf d'' then
        nf_mul u (nf_atom_inv (nf_to_rexpr d'') d'')
      else nf_atom_inv e0 d
    else nf_atom_inv e0 d
  else nf_atom_inv e0 d.

(* inverse of d, the normal form of e0 *)
Definition nf_inv (e0 : rexpr) (d : nf) : nf * seq cond :=
  match d with
  | [::] => ([::], [::])
  | [:: (c, (v, m))] =>
    if nf_inv_num [:: (c, ([::], m))] is Some u then
      let: (w, cs) := vinv v in (nf_mul u w, cs)
    else (nf_atom_inv e0 d, [::])
  | _ =>
    if novar d then
      if nf_inv_num d is Some u then (u, [::]) else (nf_atom_inv e0 d, [::])
    else (nf_atom_inv_m e0 d, [::])
  end.

Definition atom_inv_nf0 (a : atom) : nf :=
  match a with
  | AVar i => atom_nf (AInv (RVar i))
  | AInv e => pnorm0 e
  | ARoot n e => atom_nf (AInv (RRootE n e))
  end.

Definition vinv0 (v : vmono) : nf :=
  foldr (fun ak acc => nf_mul0 (nf_pow0 (atom_inv_nf0 ak.1) ak.2) acc) nf_one v.

Definition nf_atom_inv0 (d : nf) : nf :=
  let: (c, d') := nf_prim d in
  if prim_ok d c d' then nf_scale (c_inv c) (atom_nf (AInv (nf_to_rexpr0 d')))
  else atom_nf (AInv (nf_to_rexpr0 d)).

Definition nf_inv0 (d : nf) : nf :=
  match d with
  | [::] => [::]
  | [:: (c, (v, _))] =>
    if c_is0 c then [::] else nf_mul0 [:: (c_inv c, ([::], [::]))] (vinv0 v)
  | _ => nf_atom_inv0 d
  end.

Local Open Scope ring_scope.

Section InverseSound.

Variable F : numFieldType.
Variable r : posroot F.
Variable env : seq F.

Local Notation fct_interp := (fct_interp r).
Local Notation mono_interp := (mono_interp r).
Local Notation atom_interp := (atom_interp r env).
Local Notation vmono_interp := (vmono_interp r env).
Local Notation key_interp := (key_interp r env).
Local Notation holds := (holds r env).
Local Notation nf_interp := (nf_interp r env).

Local Arguments nf_mul : simpl never.
Local Arguments nf_add : simpl never.
Local Arguments nf_pow : simpl never.
Local Arguments nf_opp : simpl never.

Lemma atom_inv_nf_sound a : holds (atom_inv_nf a).2 ->
  nf_interp (atom_inv_nf a).1 = (atom_interp a)^-1.
Proof.
case: a => [i|e|n e] /=.
- by rewrite nf_atom1.
- by rewrite -pnorm_sound invrK.
case/holds_cons => /= He _.
have N0 : (0 < Pos.to_nat n)%N by apply/ssrnat.ltP; exact: Pos2Nat.is_pos.
rewrite nf_interp_cons nf_interp_nil /key_interp /=.
rewrite vmono_mul_sound vsingle_sound.
rewrite vmono_interp_cons vmono_interp_nil mono_interp_nil C2F_c_one /= expr1.
rewrite !mulr1 mul1r addr0.
by rewrite -{2}(prootK r N0 He) exprVpred.
Qed.

Lemma vinv_sound v :
  holds (vinv v).2 -> nf_interp (vinv v).1 = (vmono_interp v)^-1.
Proof.
elim: v => [|[a k] v IH] /=.
  by rewrite nf_one_sound vmono_interp_nil invr1.
move: IH; rewrite /vinv /=; case: (foldr _ _ v) => q cs /= IH.
have := @atom_inv_nf_sound a; case: (atom_inv_nf a) => qa csa /= Ha.
case/holds_cat => /Ha Hqa /IH Hq.
by rewrite nf_mul_sound nf_pow_sound Hqa Hq vmono_interp_cons invfM exprVn.
Qed.

Lemma nf_inv_num_sound d u :
  nf_inv_num d = Some u -> nf_interp u = (nf_interp d)^-1.
Proof.
rewrite /nf_inv_num; case: nf_inv_cand => [u'|] //.
case: ifP => // /nf_eqb_eq H [<-].
have H1 : nf_interp d * nf_interp u' = 1.
  by rewrite -nf_mul_sound H nf_one_sound.
have nz : nf_interp d != 0.
  apply/eqP => H0; move: H1; rewrite H0 mul0r => /eqP.
  by rewrite eq_sym oner_eq0.
by rewrite -[RHS]mulr1 -H1 mulKf.
Qed.

Lemma nf_scale_sound c p : nf_interp (nf_scale c p) = C2F c * nf_interp p.
Proof.
elim: p => [|t p IH] /=; first by rewrite !nf_interp_nil mulr0.
by rewrite !nf_interp_cons IH C2F_c_mul mulrDr mulrA.
Qed.

Lemma prim_ok_sound d c d' :
  prim_ok d c d' -> nf_interp d = C2F c * nf_interp d'.
Proof. by case/andP => _ /nf_eqb_eq ->; rewrite nf_scale_sound. Qed.

Lemma nf_atom_inv_sound e0 d : rinterp r env e0 = nf_interp d ->
  nf_interp (nf_atom_inv e0 d) = (nf_interp d)^-1.
Proof.
move=> He; rewrite /nf_atom_inv; case: nf_prim => c d'.
case: ifP => [/andP[Hok Hw]|_].
  rewrite nf_scale_sound /atom_nf nf_atom1 /= (nf_to_rexpr_sound _ _ Hw).
  by rewrite C2F_c_inv (prim_ok_sound Hok) [RHS]invfM.
rewrite nf_atom1 /=.
by case: ifP => [/nf_to_rexpr_sound -> | _]; rewrite ?He.
Qed.

Lemma nf_atom_inv_m_sound e0 d : rinterp r env e0 = nf_interp d ->
  nf_interp (nf_atom_inv_m e0 d) = (nf_interp d)^-1.
Proof.
move=> He; rewrite /nf_atom_inv_m.
case: nf_mono_split => [[M d'']|]; last exact: nf_atom_inv_sound.
case E : (nf_inv_num M) => [u|]; last exact: nf_atom_inv_sound.
case: ifP => [/andP[/nf_eqb_eq Hd Hw]|_]; last exact: nf_atom_inv_sound.
rewrite nf_mul_sound (nf_inv_num_sound E).
rewrite nf_atom_inv_sound ?nf_to_rexpr_sound //.
by rewrite Hd nf_mul_sound [RHS]invfM.
Qed.

Lemma nf_inv_sound e0 d :
  rinterp r env e0 = nf_interp d -> holds (nf_inv e0 d).2 ->
  nf_interp (nf_inv e0 d).1 = (nf_interp d)^-1.
Proof.
move=> He; case: d He => [|[c [v m]] [|t2 d]] He /=.
- by rewrite nf_interp_nil invr0.
- case E : (nf_inv_num _) => [u|]; last by rewrite nf_atom_inv_sound.
  have := @vinv_sound v; case: (vinv v) => w cs /= Hw /Hw {}Hw.
  rewrite nf_mul_sound (nf_inv_num_sound E) Hw.
  rewrite !nf_interp_cons !nf_interp_nil !addr0.
  rewrite /key_interp /= vmono_interp_nil mul1r -invfM; congr (_^-1).
  by rewrite -mulrA (mulrC (mono_interp m)).
case: ifP => _ /=; last by move=> _; rewrite nf_atom_inv_m_sound.
case E : (nf_inv_num _) => [u|] /= _; last by rewrite nf_atom_inv_sound.
exact: nf_inv_num_sound E.
Qed.

End InverseSound.

Section InverseSound0.

Variable F : numFieldType.
Variable rt : nat -> F -> F.
Variable env : seq F.

Local Notation ri := (rinterp_gen rt env).
Local Notation atom_interp0 := (atom_interp0 rt env).
Local Notation vmono_interp0 := (vmono_interp0 rt env).
Local Notation holds0 := (holds0 rt env).
Local Notation nf_interp0 := (nf_interp0 rt env).

Local Arguments nf_add : simpl never.
Local Arguments nf_mul0 : simpl never.

Lemma atom_inv_nf0_sound a : nf_interp0 (atom_inv_nf0 a) = (atom_interp0 a)^-1.
Proof.
case: a => [i|e|n e] /=; rewrite ?atom_nf_sound0 //.
by rewrite -pnorm0_sound invrK.
Qed.

Lemma vinv0_sound v : nf_interp0 (vinv0 v) = (vmono_interp0 v)^-1.
Proof.
elim: v => [|[a k] v IH] /=.
  by rewrite nf_one_sound0 vmono_interp0_nil invr1.
rewrite nf_mul0_sound nf_pow0_sound atom_inv_nf0_sound IH vmono_interp0_cons.
by rewrite invfM exprVn.
Qed.

Lemma nf_scale_sound0 c p : nf_interp0 (nf_scale c p) = C2F c * nf_interp0 p.
Proof.
elim: p => [|t p IH] /=; first by rewrite !nf_interp0_nil mulr0.
by rewrite !nf_interp0_cons IH C2F_c_mul mulrDr mulrA.
Qed.

Lemma prim_ok_sound0 d c d' :
  prim_ok d c d' -> nf_interp0 d = C2F c * nf_interp0 d'.
Proof. by case/andP => _ /nf_eqb_eq0 ->; rewrite nf_scale_sound0. Qed.

Lemma nf_atom_inv0_sound d : nf_interp0 (nf_atom_inv0 d) = (nf_interp0 d)^-1.
Proof.
rewrite /nf_atom_inv0; case: nf_prim => c d'; case: ifP => [Hok|_]; last first.
  by rewrite atom_nf_sound0 /= nf_to_rexpr0_sound.
by rewrite nf_scale_sound0 atom_nf_sound0 /= nf_to_rexpr0_sound C2F_c_inv
  (prim_ok_sound0 Hok) [RHS]invfM.
Qed.

Local Arguments nf_atom_inv0 : simpl never.

Lemma nf_inv0_sound d : nf_interp0 (nf_inv0 d) = (nf_interp0 d)^-1.
Proof.
case: d => [|[c [v m]] [|t2 d]] /=.
- by rewrite nf_interp0_nil invr0.
- rewrite nf_interp0_cons nf_interp0_nil addr0 /=.
  case: ifP => [/(@c_is0P F _) ->|_].
    by rewrite nf_interp0_nil mul0r invr0.
  rewrite nf_mul0_sound vinv0_sound nf_interp0_cons nf_interp0_nil addr0 /=.
  by rewrite vmono_interp0_nil C2F_c_inv mulr1 [RHS]invfM.
exact: nf_atom_inv0_sound.
Qed.

End InverseSound0.

End InverseF.
