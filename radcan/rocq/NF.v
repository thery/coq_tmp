(******************************************************************************)
(* NF: normal forms, sorted lists of (coefficient, key), in module NFF N.     *)
(*   nf_add, nf_mul, nf_pow, ... == arithmetic on normal forms                *)
(*   nf_to_rexpr p     == p printed back as an expression                     *)
(*   pnorm e           == structural normalisation (no simplification, no     *)
(*                        side condition)                                     *)
(*   nf_mul0, pnorm0, nf_to_rexpr0 == root-free variants (root monomials      *)
(*                        ignored), for the root-free normaliser              *)
(*   nf_interp r env p == value of the normal form p                          *)
(*   nf_interp0 rt env p == value ignoring root monomials                     *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt ZArith Lia.
From Stdlib Require Import QArith_base Qreduction.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts Syntax Backend Mono Factor.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module NFF (Import N : NUM).

Include FactorF N.

Definition nf := seq (coef * key).

Definition nf_single (c : coef) (m : key) : nf :=
  if c_is0 c then [::] else [:: (c, m)].

Fixpoint nf_add (p1 p2 : nf) {struct p1} : nf :=
  match p1 with
  | [::] => p2
  | (c1, m1) :: p1' =>
    let fix aux (p2 : nf) : nf :=
      match p2 with
      | [::] => p1
      | (c2, m2) :: p2' =>
        match key_cmp m1 m2 with
        | Lt => (c1, m1) :: nf_add p1' p2
        | Gt => (c2, m2) :: aux p2'
        | Eq => let c := c_add c1 c2 in
                if c_is0 c then nf_add p1' p2' else (c, m1) :: nf_add p1' p2'
        end
      end in aux p2
  end.

Definition nf_opp (p : nf) : nf := map (fun t => (c_opp t.1, t.2)) p.

Definition nf_mul_term (c : coef) (k : key) (p : nf) : nf :=
  foldr (fun t acc => let: (c', m') := mono_mul k.2 t.2.2 in
                      nf_add (nf_single (c_mul (c_mul c t.1) (c_of_int c'))
                                        (vmono_mul k.1 t.2.1, m')) acc)
        [::] p.

Definition nf_mul (p1 p2 : nf) : nf :=
  foldr (fun t acc => nf_add (nf_mul_term t.1 t.2 p2) acc) [::] p1.

Definition nf_one : nf := [:: (c_one, ([::], [::]))].

(* binary powering *)
Fixpoint nf_pow_pos (p : nf) (k : positive) : nf :=
  match k with
  | xH => p
  | xO k => let q := nf_pow_pos p k in nf_mul q q
  | xI k => let q := nf_pow_pos p k in nf_mul p (nf_mul q q)
  end.

Definition nf_pow (p : nf) (k : nat) : nf :=
  if k is O then nf_one else nf_pow_pos p (Pos.of_nat k).

Definition nf_root (n p : positive) : nf :=
  let: (c, m) := root_cm (Pos.to_nat n) (cfactor p) in
  nf_single (c_of_int c) ([::], m).

Fixpoint nf_eqb (p1 p2 : nf) : bool :=
  match p1, p2 with
  | [::], [::] => true
  | t1 :: p1', t2 :: p2' =>
     [&& c_eqb t1.1 t2.1,
         cmp_eqb (key_cmp t1.2 t2.2) & nf_eqb p1' p2']
  | _, _ => false
  end.

(* Printing normal forms back to syntax *)

Fixpoint rprod (l : seq rexpr) : rexpr :=
  match l with
  | [::] => RCst Z1
  | a :: l' => if l' is [::] then a else RMul a (rprod l')
  end.

Fixpoint rsum (l : seq rexpr) : rexpr :=
  match l with
  | [::] => RCst Z0
  | a :: l' => if l' is [::] then a else RAdd a (rsum l')
  end.

Definition q_to_rexpr (q : coef) : rexpr :=
  let q' := c_to_Q q in
  if p_eqb (Qden q') xH then RCst (Qnum q')
  else RMul (RCst (Qnum q')) (RInv (RCst (Zpos (Qden q')))).

Definition atom_to_rexpr (a : atom) : rexpr :=
  match a with
  | AVar i => RVar i | AInv e => RInv e | ARoot n e => RRootE n e
  end.

Definition rpow (e : rexpr) (k : nat) : rexpr :=
  if k == 1%N then e else RPow e k.

Definition term_to_rexpr (t : coef * key) : rexpr :=
  let fs := map (fun ak => rpow (atom_to_rexpr ak.1) ak.2) t.2.1 ++
            map (fun f => rpow (RRoot (Pos.of_nat f.1.2) f.1.1) f.2) t.2.2 in
  if c_eqb t.1 c_one then rprod fs
  else rprod (q_to_rexpr t.1 :: fs).

Definition nf_to_rexpr (p : nf) : rexpr := rsum (map term_to_rexpr (rev p)).

Definition nf_wf (p : nf) : bool :=
  all (fun t => all (fun f => (0 < f.1.2)%N) t.2.2) p.

(* Structural normalisation *)

Fixpoint pnorm (e : rexpr) : nf :=
  match e with
  | RCst z => nf_single (c_of_Z z) ([::], [::])
  | RVar i => [:: (c_one, ([:: (AVar i, 1%N)], [::]))]
  | RRoot n p => nf_root n p
  | RRootE n e1 => [:: (c_one, ([:: (ARoot n e1, 1%N)], [::]))]
  | RAdd e1 e2 => nf_add (pnorm e1) (pnorm e2)
  | ROpp e1 => nf_opp (pnorm e1)
  | RSub e1 e2 => nf_add (pnorm e1) (nf_opp (pnorm e2))
  | RMul e1 e2 => nf_mul (pnorm e1) (pnorm e2)
  | RPow e1 k => nf_pow (pnorm e1) k
  | RInv e1 =>
    match e1 with
    | RCst Z0 => [::]
    | RCst (Zpos d) => [:: (c_inv (c_of_Z (Zpos d)), ([::], [::]))]
    | RCst (Zneg d) => [:: (c_opp (c_inv (c_of_Z (Zpos d))), ([::], [::]))]
    | _ => [:: (c_one, ([:: (AInv e1, 1%N)], [::]))]
    end
  end.

Definition nf_mul_term0 (c : coef) (v : vmono) (p : nf) : nf :=
  foldr (fun t acc =>
           nf_add (nf_single (c_mul c t.1) (vmono_mul v t.2.1, [::])) acc)
        [::] p.

Definition nf_mul0 (p1 p2 : nf) : nf :=
  foldr (fun t acc => nf_add (nf_mul_term0 t.1 t.2.1 p2) acc) [::] p1.

Fixpoint nf_pow_pos0 (p : nf) (k : positive) : nf :=
  match k with
  | xH => p
  | xO k => let q := nf_pow_pos0 p k in nf_mul0 q q
  | xI k => let q := nf_pow_pos0 p k in nf_mul0 p (nf_mul0 q q)
  end.

Definition nf_pow0 (p : nf) (k : nat) : nf :=
  if k is O then nf_one else nf_pow_pos0 p (Pos.of_nat k).

Definition atom_nf (a : atom) : nf := [:: (c_one, ([:: (a, 1%N)], [::]))].

Fixpoint pnorm0 (e : rexpr) : nf :=
  match e with
  | RCst z => nf_single (c_of_Z z) ([::], [::])
  | RVar i => atom_nf (AVar i)
  | RRoot n p => atom_nf (ARoot n (RCst (Zpos p)))
  | RRootE n e1 => atom_nf (ARoot n e1)
  | RAdd e1 e2 => nf_add (pnorm0 e1) (pnorm0 e2)
  | ROpp e1 => nf_opp (pnorm0 e1)
  | RSub e1 e2 => nf_add (pnorm0 e1) (nf_opp (pnorm0 e2))
  | RMul e1 e2 => nf_mul0 (pnorm0 e1) (pnorm0 e2)
  | RPow e1 k => nf_pow0 (pnorm0 e1) k
  | RInv e1 =>
    match e1 with
    | RCst Z0 => [::]
    | RCst (Zpos d) => [:: (c_inv (c_of_Z (Zpos d)), ([::], [::]))]
    | RCst (Zneg d) => [:: (c_opp (c_inv (c_of_Z (Zpos d))), ([::], [::]))]
    | _ => atom_nf (AInv e1)
    end
  end.

(* printing, ignoring root monomials *)
Definition nf_to_rexpr0 (p : nf) : rexpr :=
  rsum (map (fun t => term_to_rexpr (t.1, (t.2.1, [::]))) (rev p)).

Local Open Scope ring_scope.

Section NFSound.

Variable F : numFieldType.
Variable r : posroot F.
Variable env : seq F.

Local Notation fct_interp := (fct_interp r).
Local Notation mono_interp := (mono_interp r).
Local Notation atom_interp := (atom_interp r env).
Local Notation vmono_interp := (vmono_interp r env).
Local Notation key_interp := (key_interp r env).
Local Notation holds := (holds r env).


Definition nf_interp (p : nf) : F := \sum_(t <- p) C2F t.1 * key_interp t.2.

Lemma nf_interp_nil : nf_interp [::] = 0.
Proof. by rewrite /nf_interp big_nil. Qed.

Lemma nf_interp_cons t p :
  nf_interp (t :: p) = C2F t.1 * key_interp t.2 + nf_interp p.
Proof. by rewrite /nf_interp big_cons. Qed.

Lemma nf_single_sound c k : nf_interp (nf_single c k) = C2F c * key_interp k.
Proof.
rewrite /nf_single; case: ifP => [/(@c_is0P F _) ->|_].
  by rewrite nf_interp_nil mul0r.
by rewrite nf_interp_cons nf_interp_nil addr0.
Qed.

Lemma nf_add_sound p1 p2 :
  nf_interp (nf_add p1 p2) = nf_interp p1 + nf_interp p2.
Proof.
elim: p1 p2 => [|[c1 m1] p1 IH1] p2 /=; first by rewrite nf_interp_nil add0r.
elim: p2 => [|[c2 m2] p2 IH2] /=; first by rewrite nf_interp_nil addr0.
case E : (key_cmp m1 m2).
- rewrite -(key_cmp_eq E); case: ifP => [/(@c_is0P F _)|_].
    rewrite C2F_c_add IH1 !nf_interp_cons /= => H.
    by rewrite addrACA -mulrDl H mul0r add0r.
  by rewrite !nf_interp_cons /= IH1 C2F_c_add mulrDl addrACA.
- by rewrite !nf_interp_cons IH1 nf_interp_cons addrA.
by rewrite !nf_interp_cons IH2 nf_interp_cons addrCA.
Qed.

Lemma nf_opp_sound p : nf_interp (nf_opp p) = - nf_interp p.
Proof.
elim: p => [|[c m] p IH] /=; first by rewrite nf_interp_nil oppr0.
by rewrite !nf_interp_cons IH /= C2F_c_opp mulNr opprD.
Qed.

Lemma nf_mul_term_sound c k p :
  nf_interp (nf_mul_term c k p) = C2F c * key_interp k * nf_interp p.
Proof.
case: k => v m; elim: p => [|[c2 [v2 m2]] p IH] /=.
  by rewrite nf_interp_nil mulr0.
have := mono_mul_sound r m m2; case: (mono_mul m m2) => c' m' /= H.
rewrite nf_add_sound nf_single_sound IH nf_interp_cons /= mulrDr; congr (_ + _).
rewrite /key_interp /= vmono_mul_sound !C2F_c_mul C2F_c_of_int.
move: (C2F c) (C2F c2) (vmono_interp v) (vmono_interp v2) => a b x y.
rewrite mulrACA H -!mulrA; congr (_ * _); rewrite mulrCA; congr (_ * _).
by rewrite [RHS]mulrCA; congr (_ * _); exact: mulrCA.
Qed.

Lemma nf_mul_sound p1 p2 :
  nf_interp (nf_mul p1 p2) = nf_interp p1 * nf_interp p2.
Proof.
elim: p1 => [|[c m] p1 IH] /=; first by rewrite nf_interp_nil mul0r.
by rewrite nf_add_sound nf_mul_term_sound IH nf_interp_cons mulrDl.
Qed.

Lemma nf_one_sound : nf_interp nf_one = 1.
Proof.
rewrite nf_interp_cons nf_interp_nil /key_interp /= vmono_interp_nil.
by rewrite mono_interp_nil C2F_c_one !mulr1 addr0.
Qed.

Lemma nf_pow_pos_sound p k :
  nf_interp (nf_pow_pos p k) = nf_interp p ^+ Pos.to_nat k.
Proof.
elim: k => [k IH|k IH|] /=; last by rewrite expr1.
  by rewrite Pos2Nat.inj_xI !nf_mul_sound IH -exprD addnn -mul2n exprS.
by rewrite Pos2Nat.inj_xO !nf_mul_sound IH -exprD addnn -mul2n.
Qed.

Lemma nf_pow_sound p k : nf_interp (nf_pow p k) = nf_interp p ^+ k.
Proof.
case: k => [|k]; first by rewrite /= nf_one_sound.
by rewrite /nf_pow nf_pow_pos_sound Nat2Pos.id.
Qed.

Lemma nf_root_sound n p :
  nf_interp (nf_root n p) = proot r (Pos.to_nat n) (pos2F F p).
Proof.
have n0 : (0 < Pos.to_nat n)%N by apply/ssrnat.ltP; exact: Pos2Nat.is_pos.
rewrite /nf_root; have := root_cm_sound r (cfactor p) n0.
case: root_cm => c m /= H.
rewrite nf_single_sound /key_interp /= vmono_interp_nil mul1r C2F_c_of_int H.
by rewrite -cfactor_sound.
Qed.

Lemma nf_eqb_eq p1 p2 : nf_eqb p1 p2 -> nf_interp p1 = nf_interp p2.
Proof.
elim: p1 p2 => [|[c1 k1] p1 IH] [|[c2 k2] p2] //=.
case/and3P => /(@c_eqbP F _ _) Hc /cmp_eqbP/key_cmp_eq <- /IH Hp.
by rewrite !nf_interp_cons /= Hc Hp.
Qed.

(* reading a normal form back as an expression *)

Lemma rprod_sound l : rinterp r env (rprod l) = \prod_(e <- l) rinterp r env e.
Proof.
elim: l => [|a l IH] /=; first by rewrite big_nil pos2F1.
by case: l IH => [|b l] IH; rewrite ?big_seq1 // big_cons -IH.
Qed.

Lemma rsum_sound l : rinterp r env (rsum l) = \sum_(e <- l) rinterp r env e.
Proof.
elim: l => [|a l IH] /=; first by rewrite big_nil.
by case: l IH => [|b l] IH; rewrite ?big_seq1 // big_cons -IH.
Qed.

Lemma q_to_rexpr_sound q : rinterp r env (q_to_rexpr q) = C2F q.
Proof.
rewrite /q_to_rexpr /C2F; case: (c_to_Q q) => n d; rewrite /Q2F /p_eqb /=.
by case: d => [d|d|] //=; rewrite pos2F1 divr1.
Qed.

Lemma rpow_sound e k : rinterp r env (rpow e k) = rinterp r env e ^+ k.
Proof. by rewrite /rpow; case: eqP => [->|] //=; rewrite expr1. Qed.

Lemma atom_to_rexpr_sound a : rinterp r env (atom_to_rexpr a) = atom_interp a.
Proof. by case: a. Qed.

Lemma term_to_rexpr_sound t : all (fun f => 0 < f.1.2)%N t.2.2 ->
  rinterp r env (term_to_rexpr t) = C2F t.1 * key_interp t.2.
Proof.
case: t => c [v m] /= wm.
have Hf : rinterp r env (rprod
   (map (fun ak => rpow (atom_to_rexpr ak.1) ak.2) v ++
    map (fun f => rpow (RRoot (Pos.of_nat f.1.2) f.1.1) f.2) m)) =
   key_interp (v, m).
  rewrite rprod_sound big_cat !big_map.
  rewrite /key_interp /vmono_interp /mono_interp /=.
  congr (_ * _).
    by apply: eq_bigr => ak _; rewrite rpow_sound atom_to_rexpr_sound.
  elim: m wm => [|[[b n] e] m IH] /=; first by rewrite !big_nil.
  case/andP => n0 /IH; rewrite !big_cons => ->.
  rewrite rpow_sound /= Nat2Pos.id //.
  by move: n0; case: n.
have Hg : rinterp r env (rprod (q_to_rexpr c ::
   ([seq rpow (atom_to_rexpr ak.1) ak.2 | ak <- v] ++
    [seq rpow (RRoot (Pos.of_nat f.1.2) f.1.1) f.2 | f <- m]))) =
   C2F c * key_interp (v, m).
  by rewrite rprod_sound big_cons -rprod_sound Hf q_to_rexpr_sound.
rewrite /term_to_rexpr; case: ifP => [/(@c_eqbP F _ _) Ec|_]; last exact: Hg.
by rewrite Hf Ec C2F_c_one mul1r.
Qed.

Lemma nf_to_rexpr_sound p :
  nf_wf p -> rinterp r env (nf_to_rexpr p) = nf_interp p.
Proof.
rewrite /nf_to_rexpr rsum_sound big_map big_rev /nf_interp.
elim: p => [|t p IH] /=; first by rewrite !big_nil.
by case/andP => wt /IH; rewrite !big_cons term_to_rexpr_sound // => ->.
Qed.

Lemma nf_atom1 a :
  nf_interp [:: (c_one, ([:: (a, 1%N)], [::]))] = atom_interp a.
Proof.
rewrite nf_interp_cons nf_interp_nil /key_interp /= vmono_interp_cons.
by rewrite vmono_interp_nil mono_interp_nil C2F_c_one !mulr1 mul1r addr0 expr1.
Qed.

(* structural normalisation *)

Lemma pnorm_sound e : rinterp r env e = nf_interp (pnorm e).
Proof.
elim: e => [z|i|n p|n e1 IH1|e1 IH1 e2 IH2|e1 IH1|e1 IH1 e2 IH2|e1 IH1 e2 IH2|
            e1 IH1 k|e1 IH1] /=.
- rewrite nf_single_sound /key_interp /= vmono_interp_nil mono_interp_nil.
  by rewrite !mulr1 C2F_c_of_Z.
- by rewrite nf_atom1.
- by rewrite nf_root_sound.
- by rewrite nf_atom1.
- by rewrite nf_add_sound IH1 IH2.
- by rewrite nf_opp_sound IH1.
- by rewrite nf_add_sound nf_opp_sound IH1 IH2.
- by rewrite nf_mul_sound IH1 IH2.
- by rewrite nf_pow_sound IH1.
have Hat := nf_atom1 (AInv e1).
case: e1 IH1 Hat => // [[|d|d]] _ Hat /=; rewrite ?nf_interp_nil ?invr0 //.
  rewrite nf_interp_cons nf_interp_nil /key_interp /= vmono_interp_nil.
  rewrite mono_interp_nil ?C2F_c_opp C2F_c_inv C2F_c_of_Z /=.
  by rewrite !mulr1 ?mul1r addr0.
rewrite nf_interp_cons nf_interp_nil /key_interp /= vmono_interp_nil.
rewrite mono_interp_nil C2F_c_opp C2F_c_inv C2F_c_of_Z /=.
by rewrite !mulr1 addr0 ?invrN.
Qed.

End NFSound.

Section NFSound0.

Variable F : numFieldType.
Variable rt : nat -> F -> F.
Variable env : seq F.

Local Notation ri := (rinterp_gen rt env).
Local Notation atom_interp0 := (atom_interp0 rt env).
Local Notation vmono_interp0 := (vmono_interp0 rt env).
Local Notation holds0 := (holds0 rt env).

Definition nf_interp0 (p : nf) : F :=
  \sum_(t <- p) C2F t.1 * vmono_interp0 t.2.1.

Lemma nf_interp0_nil : nf_interp0 [::] = 0.
Proof. by rewrite /nf_interp0 big_nil. Qed.

Lemma nf_interp0_cons t p :
  nf_interp0 (t :: p) = C2F t.1 * vmono_interp0 t.2.1 + nf_interp0 p.
Proof. by rewrite /nf_interp0 big_cons. Qed.

Lemma nf_eqb_eq0 p1 p2 : nf_eqb p1 p2 -> nf_interp0 p1 = nf_interp0 p2.
Proof.
elim: p1 p2 => [|[c1 k1] p1 IH] [|[c2 k2] p2] //=.
case/and3P => /(@c_eqbP F _ _) Hc /cmp_eqbP/key_cmp_eq <- /IH Hp.
by rewrite !nf_interp0_cons /= Hc Hp.
Qed.

Lemma nf_single_sound0 c k :
  nf_interp0 (nf_single c k) = C2F c * vmono_interp0 k.1.
Proof.
rewrite /nf_single; case: ifP => [/(@c_is0P F _) ->|_].
  by rewrite nf_interp0_nil mul0r.
by rewrite nf_interp0_cons nf_interp0_nil addr0.
Qed.

Lemma nf_add_sound0 p1 p2 :
  nf_interp0 (nf_add p1 p2) = nf_interp0 p1 + nf_interp0 p2.
Proof.
elim: p1 p2 => [|[c1 m1] p1 IH1] p2 /=; first by rewrite nf_interp0_nil add0r.
elim: p2 => [|[c2 m2] p2 IH2] /=; first by rewrite nf_interp0_nil addr0.
case E : (key_cmp m1 m2).
- rewrite -(key_cmp_eq E); case: ifP => [/(@c_is0P F _)|_].
    rewrite C2F_c_add IH1 !nf_interp0_cons /= => H.
    by rewrite addrACA -mulrDl H mul0r add0r.
  by rewrite !nf_interp0_cons /= IH1 C2F_c_add mulrDl addrACA.
- by rewrite !nf_interp0_cons IH1 nf_interp0_cons addrA.
by rewrite !nf_interp0_cons IH2 nf_interp0_cons addrCA.
Qed.

Lemma nf_opp_sound0 p : nf_interp0 (nf_opp p) = - nf_interp0 p.
Proof.
elim: p => [|[c m] p IH] /=; first by rewrite nf_interp0_nil oppr0.
by rewrite !nf_interp0_cons IH /= C2F_c_opp mulNr opprD.
Qed.

Local Arguments nf_add : simpl never.

Lemma nf_mul_term0_sound c v p :
  nf_interp0 (nf_mul_term0 c v p) = C2F c * vmono_interp0 v * nf_interp0 p.
Proof.
elim: p => [|[c2 [v2 m2]] p IH] /=; first by rewrite nf_interp0_nil mulr0.
rewrite nf_add_sound0 nf_single_sound0 IH nf_interp0_cons /= mulrDr.
congr (_ + _).
rewrite vmono_mul_sound0 C2F_c_mul.
move: (C2F c) (C2F c2) (vmono_interp0 v) (vmono_interp0 v2) => a b x y.
by rewrite mulrACA.
Qed.

Lemma nf_mul0_sound p1 p2 :
  nf_interp0 (nf_mul0 p1 p2) = nf_interp0 p1 * nf_interp0 p2.
Proof.
elim: p1 => [|[c [v m]] p1 IH] /=; first by rewrite nf_interp0_nil mul0r.
by rewrite nf_add_sound0 nf_mul_term0_sound IH nf_interp0_cons mulrDl.
Qed.

Lemma nf_one_sound0 : nf_interp0 nf_one = 1.
Proof.
rewrite nf_interp0_cons nf_interp0_nil /= vmono_interp0_nil.
by rewrite C2F_c_one mulr1 addr0.
Qed.

Local Arguments nf_mul0 : simpl never.

Lemma nf_pow_pos0_sound p k :
  nf_interp0 (nf_pow_pos0 p k) = nf_interp0 p ^+ Pos.to_nat k.
Proof.
elim: k => [k IH|k IH|] /=; last by rewrite expr1.
  by rewrite Pos2Nat.inj_xI !nf_mul0_sound IH -exprD addnn -mul2n exprS.
by rewrite Pos2Nat.inj_xO !nf_mul0_sound IH -exprD addnn -mul2n.
Qed.

Lemma nf_pow0_sound p k : nf_interp0 (nf_pow0 p k) = nf_interp0 p ^+ k.
Proof.
case: k => [|k]; first by rewrite /= nf_one_sound0.
by rewrite /nf_pow0 nf_pow_pos0_sound Nat2Pos.id.
Qed.

Lemma atom_nf_sound0 a : nf_interp0 (atom_nf a) = atom_interp0 a.
Proof.
rewrite /atom_nf nf_interp0_cons nf_interp0_nil /= vmono_interp0_cons.
by rewrite vmono_interp0_nil C2F_c_one mulr1 mul1r addr0 expr1.
Qed.

Lemma pnorm0_sound e : ri e = nf_interp0 (pnorm0 e).
Proof.
elim: e => [z|i|n p|n e1 IH1|e1 IH1 e2 IH2|e1 IH1|e1 IH1 e2 IH2|e1 IH1 e2 IH2|
            e1 IH1 k|e1 IH1] /=.
- by rewrite nf_single_sound0 /= vmono_interp0_nil mulr1 C2F_c_of_Z.
- by rewrite atom_nf_sound0.
- by rewrite atom_nf_sound0.
- by rewrite atom_nf_sound0.
- by rewrite nf_add_sound0 IH1 IH2.
- by rewrite nf_opp_sound0 IH1.
- by rewrite nf_add_sound0 nf_opp_sound0 IH1 IH2.
- by rewrite nf_mul0_sound IH1 IH2.
- by rewrite nf_pow0_sound IH1.
have Hat := atom_nf_sound0 (AInv e1).
case: e1 IH1 Hat => // [[|d|d]] _ Hat /=; rewrite ?nf_interp0_nil ?invr0 //.
  rewrite nf_interp0_cons nf_interp0_nil /= vmono_interp0_nil.
  by rewrite ?C2F_c_opp C2F_c_inv C2F_c_of_Z /= !mulr1 ?mul1r addr0.
rewrite nf_interp0_cons nf_interp0_nil /= vmono_interp0_nil.
by rewrite C2F_c_opp C2F_c_inv C2F_c_of_Z /= !mulr1 addr0 ?invrN.
Qed.

Lemma rprod_sound0 l : ri (rprod l) = \prod_(e <- l) ri e.
Proof.
elim: l => [|a l IH] /=; first by rewrite big_nil pos2F1.
by case: l IH => [|b l] IH; rewrite ?big_seq1 // big_cons -IH.
Qed.

Lemma rsum_sound0 l : ri (rsum l) = \sum_(e <- l) ri e.
Proof.
elim: l => [|a l IH] /=; first by rewrite big_nil.
by case: l IH => [|b l] IH; rewrite ?big_seq1 // big_cons -IH.
Qed.

Lemma q_to_rexpr_sound0 q : ri (q_to_rexpr q) = C2F q.
Proof.
rewrite /q_to_rexpr /C2F; case: (c_to_Q q) => n d; rewrite /Q2F /p_eqb /=.
by case: d => [d|d|] //=; rewrite pos2F1 divr1.
Qed.

Lemma rpow_sound0 e k : ri (rpow e k) = ri e ^+ k.
Proof. by rewrite /rpow; case: eqP => [->|] //=; rewrite expr1. Qed.

Lemma atom_to_rexpr_sound0 a : ri (atom_to_rexpr a) = atom_interp0 a.
Proof. by case: a. Qed.

Lemma term_to_rexpr_sound0 c v :
  ri (term_to_rexpr (c, (v, [::]))) = C2F c * vmono_interp0 v.
Proof.
have Hf : ri (rprod
   (map (fun ak => rpow (atom_to_rexpr ak.1) ak.2) v ++
    map (fun f => rpow (RRoot (Pos.of_nat f.1.2) f.1.1) f.2) [::])) =
   vmono_interp0 v.
  rewrite cats0 rprod_sound0 big_map /vmono_interp0.
  by apply: eq_bigr => ak _; rewrite rpow_sound0 atom_to_rexpr_sound0.
have Hg : ri (rprod (q_to_rexpr c ::
   (map (fun ak => rpow (atom_to_rexpr ak.1) ak.2) v ++
    map (fun f => rpow (RRoot (Pos.of_nat f.1.2) f.1.1) f.2) [::]))) =
   C2F c * vmono_interp0 v.
  by rewrite rprod_sound0 big_cons -rprod_sound0 Hf q_to_rexpr_sound0.
rewrite /term_to_rexpr; case: ifP => [/(@c_eqbP F _ _) Ec|_]; last exact: Hg.
by rewrite Hf Ec C2F_c_one mul1r.
Qed.

Lemma nf_to_rexpr0_sound p : ri (nf_to_rexpr0 p) = nf_interp0 p.
Proof.
rewrite /nf_to_rexpr0 rsum_sound0 big_map big_rev /nf_interp0.
by apply: eq_bigr => t _; rewrite term_to_rexpr_sound0.
Qed.

End NFSound0.

End NFF.
