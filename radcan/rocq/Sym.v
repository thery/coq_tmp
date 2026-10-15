(******************************************************************************)
(* Sym: roots given by hypotheses (M15), the paper's symbolic reading.        *)
(* A symbol is a variable RVar i with a defining relation y ^+ n = B (0 < n), *)
(* B any expression; results hold for EVERY choice of the symbols.            *)
(*   srel             == (i, n, B): the relation nth 0 env i ^+ n = B         *)
(*   rels_hold rt env rels == the relations hold (a plain conjunction)        *)
(*   sym_rw rels a k  == a ^+ k rewritten by the relations: y ^+ k into       *)
(*                       B ^+ (k / n) * y ^+ (k mod n), (y^-1) ^+ k into      *)
(*                       (y ^+ n.-1 * B^-1) ^+ k (no condition: 0^-1 = 0)     *)
(*   nf_symred rels f p == these rewritings applied to p until none applies   *)
(*                       (at most f rounds)                                   *)
(*   normcs rels e    == the root-free normaliser of CondNorm.v (normc0),     *)
(*                       reducing by the relations after each operation       *)
(*   radcan_check_sym rels e1 e2 == Some cs when both sides have the same     *)
(*                       normal form (cs: cancellation conditions B != 0)     *)
(*   radcan_eq_cond_sym == its soundness, for any root function rt: only the  *)
(*                       relations are used (no multiplicativity, merging,    *)
(*                       sign law or branch of any root)                      *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot Syntax Radcan.
Import Order.TTheory GRing.Theory Num.Theory ZNum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition srel := (nat * nat * rexpr)%type.

Fixpoint sym_find (rels : seq srel) (i : nat) : option (nat * rexpr) :=
  match rels with
  | [::] => None
  | (j, n, B) :: rs =>
    if (j == i) && (0 < n)%N then Some (n, B) else sym_find rs i
  end.

(* the atoms rewritten: y ^+ k with n <= k, and y^-1 *)
Definition sym_atom (rels : seq srel) (a : atom) (k : nat) : bool :=
  match a with
  | AVar i => if sym_find rels i is Some (n, _) then (n <= k)%N else false
  | AInv (RVar i) => if sym_find rels i is Some _ then (0 < k)%N else false
  | _ => false
  end.

(* the first entry a ^+ k of v with P a k, and the rest of v *)
Fixpoint vpick (P : atom -> nat -> bool) (v : vmono) :
  option (atom * nat * vmono) :=
  match v with
  | [::] => None
  | (a, k) :: v' =>
    if P a k then Some (a, k, v') else
    if vpick P v' is Some (b, l, w) then Some (b, l, (a, k) :: w) else None
  end.

Definition vnf (v : vmono) : nf := [:: (c_one, (v, [::]))].

Definition sym_rw (rels : seq srel) (a : atom) (k : nat) : nf :=
  match a with
  | AVar i =>
    if sym_find rels i is Some (n, B) then
      nf_mul0 (vnf (vsingle a (k %% n))) (nf_pow0 (pnorm0 B) (k %/ n))
    else vnf (vsingle a k)
  | AInv (RVar i) =>
    if sym_find rels i is Some (n, B) then
      nf_pow0 (nf_mul0 (vnf (vsingle (AVar i) n.-1)) (nf_inv0 (pnorm0 B))) k
    else vnf (vsingle a k)
  | _ => vnf (vsingle a k)
  end.

Definition sym_term (rels : seq srel) (t : coef * key) : nf :=
  if vpick (sym_atom rels) t.2.1 is Some (a, k, w) then
    nf_mul0 [:: (t.1, (w, t.2.2))] (sym_rw rels a k)
  else [:: t].

Definition nf_symred1 (rels : seq srel) (p : nf) : nf :=
  foldr (fun t acc => nf_add (sym_term rels t) acc) [::] p.

Fixpoint nf_symred (rels : seq srel) (f : nat) (p : nf) : nf :=
  match f with
  | O => p
  | S f' =>
    if has (fun t => vpick (sym_atom rels) t.2.1) p then
      nf_symred rels f' (nf_symred1 rels p)
    else p
  end.

Definition sym_fuel : nat := 32.

Section Normcs.

Variable rels : seq srel.

Local Notation sr := (nf_symred rels sym_fuel).

Definition sr_cancel (p : nf) : nf * seq cond :=
  let: (s, cs) := nf_cancel0 (sr p) in (sr s, cs).

Fixpoint normcs (e : rexpr) : nf * seq cond :=
  match e with
  | RCst z => (nf_single (c_of_Z z) ([::], [::]), [::])
  | RVar i => (sr (atom_nf (AVar i)), [::])
  | RRoot n p => (atom_nf (ARoot n (RCst (Zpos p))), [::])
  | RRootE n e1 =>
    let: (p, c1) := normcs e1 in (atom_nf (ARoot n (nf_to_rexpr0 p)), c1)
  | RAdd e1 e2 =>
    let: (p1, c1) := normcs e1 in let: (p2, c2) := normcs e2 in
    let: (s, c3) := sr_cancel (nf_add p1 p2) in (s, c1 ++ c2 ++ c3)
  | ROpp e1 => let: (p, c) := normcs e1 in (nf_opp p, c)
  | RSub e1 e2 =>
    let: (p1, c1) := normcs e1 in let: (p2, c2) := normcs e2 in
    let: (s, c3) := sr_cancel (nf_add p1 (nf_opp p2)) in (s, c1 ++ c2 ++ c3)
  | RMul e1 e2 =>
    let: (p1, c1) := normcs e1 in let: (p2, c2) := normcs e2 in
    let: (s, c3) := sr_cancel (nf_mul0 p1 p2) in (s, c1 ++ c2 ++ c3)
  | RPow e1 k =>
    let: (p, c1) := normcs e1 in
    let: (s, c3) := sr_cancel (nf_pow0 p k) in (s, c1 ++ c3)
  | RInv e1 =>
    let: (p, c1) := normcs e1 in
    let: (s, c3) := sr_cancel (nf_inv0 p) in (s, c1 ++ c3)
  end.

End Normcs.

Definition radcan_check_sym (rels : seq srel) (e1 e2 : rexpr) :
  option (seq cond) :=
  let: (p1, c1) := normcs rels e1 in
  let: (p2, c2) := normcs rels e2 in
  if nf_eqb p1 p2 then Some (cdedup (c1 ++ c2)) else None.

Local Open Scope ring_scope.

Section SymSound.

Variable F : numFieldType.
Variable rt : nat -> F -> F.
Variable env : seq F.

Local Notation ri := (rinterp_gen rt env).
Local Notation atom_interp0 := (atom_interp0 rt env).
Local Notation vmono_interp0 := (vmono_interp0 rt env).
Local Notation holds0 := (holds0 rt env).
Local Notation nf_interp0 := (nf_interp0 rt env).

Fixpoint rels_hold (rels : seq srel) : Prop :=
  match rels with
  | [::] => True
  | (i, n, B) :: rs =>
    if rs is [::] then nth 0 env i ^+ n = ri B
    else nth 0 env i ^+ n = ri B /\ rels_hold rs
  end.

Variable rels : seq srel.
Hypothesis Hrels : rels_hold rels.

Lemma sym_findP i n B : sym_find rels i = Some (n, B) ->
  (0 < n)%N /\ nth 0 env i ^+ n = ri B.
Proof.
elim: rels Hrels => [|[[j m] C] rs IH] //= H.
have H1 : nth 0 env j ^+ m = ri C by case: (rs) H => // ? ? [].
have H2 : rels_hold rs by case: (rs) H => // ? ? [].
by case: ifP => [/andP[/eqP <- m0] [<- <-] //|_ /(IH H2)].
Qed.

Lemma vpick_sound P v a k w : vpick P v = Some (a, k, w) ->
  vmono_interp0 v = atom_interp0 a ^+ k * vmono_interp0 w.
Proof.
elim: v a k w => [|[b l] v IH] a k w //=.
case: ifP => _; first by case=> <- <- <-; rewrite vmono_interp0_cons.
case E : (vpick P v) => [[[b' l'] w']|] // [<- <- <-].
by rewrite !vmono_interp0_cons (IH _ _ _ E) mulrCA.
Qed.

Lemma vnf_sound v : nf_interp0 (vnf v) = vmono_interp0 v.
Proof.
by rewrite nf_interp0_cons nf_interp0_nil addr0 /= C2F_c_one mul1r.
Qed.

Lemma vsingle_sound0 a k : vmono_interp0 (vsingle a k) = atom_interp0 a ^+ k.
Proof.
case: k => [|k] /=; first by rewrite vmono_interp0_nil expr0.
by rewrite vmono_interp0_cons vmono_interp0_nil mulr1.
Qed.

(* y^-1 = y ^+ n.-1 * (y ^+ n)^-1 in any field, 0 < n *)
Lemma invr_expr_pred (y : F) n : (0 < n)%N -> y^-1 = y ^+ n.-1 * (y ^+ n)^-1.
Proof.
case: n => // n _ /=; rewrite exprS invfM.
have [->|y0] := eqVneq y 0.
  by rewrite invr0 mul0r mulr0.
by rewrite mulrCA mulfV ?expf_neq0 // mulr1.
Qed.

Local Arguments nf_add : simpl never.
Local Arguments nf_mul0 : simpl never.
Local Arguments nf_pow0 : simpl never.
Local Arguments nf_inv0 : simpl never.
Local Arguments vnf : simpl never.

Lemma sym_rw_sound a k : nf_interp0 (sym_rw rels a k) = atom_interp0 a ^+ k.
Proof.
have Hd b l : nf_interp0 (vnf (vsingle b l)) = atom_interp0 b ^+ l.
  by rewrite vnf_sound vsingle_sound0.
case: a => [i|e|n e] /=; rewrite ?Hd //.
  case E : (sym_find rels i) => [[n B]|]; last exact: Hd.
  have [n0 HB] := sym_findP E.
  rewrite nf_mul0_sound nf_pow0_sound -pnorm0_sound Hd -HB -exprM /=.
  by rewrite -exprD mulnC addnC -divn_eq.
case: e => // i; case E : (sym_find rels i) => [[n B]|]; last exact: Hd.
have [n0 HB] := sym_findP E.
rewrite nf_pow0_sound nf_mul0_sound nf_inv0_sound -pnorm0_sound Hd -HB /=.
by rewrite -invr_expr_pred.
Qed.

Lemma sym_term_sound t :
  nf_interp0 (sym_term rels t) = C2F t.1 * vmono_interp0 t.2.1.
Proof.
rewrite /sym_term; case E : vpick => [[[a k] w]|]; last first.
  by rewrite nf_interp0_cons nf_interp0_nil addr0.
rewrite nf_mul0_sound sym_rw_sound nf_interp0_cons nf_interp0_nil addr0 /=.
by rewrite (vpick_sound E) -mulrA [vmono_interp0 w * _]mulrC.
Qed.

Lemma nf_symred1_sound p : nf_interp0 (nf_symred1 rels p) = nf_interp0 p.
Proof.
elim: p => [|t p IH] //=.
by rewrite nf_add_sound0 sym_term_sound IH nf_interp0_cons.
Qed.

Lemma nf_symred_sound f p : nf_interp0 (nf_symred rels f p) = nf_interp0 p.
Proof.
elim: f p => [|f IH] p //=; case: ifP => // _.
by rewrite IH nf_symred1_sound.
Qed.

Local Notation sr := (nf_symred rels sym_fuel).
Local Arguments nf_symred : simpl never.
Local Arguments sr_cancel : simpl never.

Lemma sr_cancel_sound p : holds0 (sr_cancel rels p).2 ->
  nf_interp0 (sr_cancel rels p).1 = nf_interp0 p.
Proof.
rewrite /sr_cancel; have := @nf_cancel0_sound _ rt env (sr p).
case: nf_cancel0 => s cs /= H /H.
by rewrite !nf_symred_sound.
Qed.

Theorem normcs_sound e : holds0 (normcs rels e).2 ->
  ri e = nf_interp0 (normcs rels e).1.
Proof.
elim: e => [z|i|n p|n e1 IH1|e1 IH1 e2 IH2|e1 IH1|e1 IH1 e2 IH2|e1 IH1 e2 IH2|
            e1 IH1 k|e1 IH1] /=.
- by move=> _; rewrite nf_single_sound0 /= vmono_interp0_nil mulr1 C2F_c_of_Z.
- by move=> _; rewrite nf_symred_sound atom_nf_sound0.
- by move=> _; rewrite atom_nf_sound0.
- move: IH1; case: (normcs rels e1) => p c1 /= IH1 /IH1 He.
  by rewrite atom_nf_sound0 /= nf_to_rexpr0_sound He.
- move: IH1 IH2; case: (normcs rels e1) => p1 c1.
  case: (normcs rels e2) => p2 c2 /= IH1 IH2.
  have := @sr_cancel_sound (nf_add p1 p2); case: sr_cancel => s c3 /= Hs.
  case/holds0_cat => /IH1 -> /holds0_cat [/IH2 -> /Hs ->].
  by rewrite nf_add_sound0.
- move: IH1; case: (normcs rels e1) => p c1 /= IH1 /IH1 ->.
  by rewrite nf_opp_sound0.
- move: IH1 IH2; case: (normcs rels e1) => p1 c1.
  case: (normcs rels e2) => p2 c2 /= IH1 IH2.
  have := @sr_cancel_sound (nf_add p1 (nf_opp p2)).
  case: sr_cancel => s c3 /= Hs.
  case/holds0_cat => /IH1 -> /holds0_cat [/IH2 -> /Hs ->].
  by rewrite nf_add_sound0 nf_opp_sound0.
- move: IH1 IH2; case: (normcs rels e1) => p1 c1.
  case: (normcs rels e2) => p2 c2 /= IH1 IH2.
  have := @sr_cancel_sound (nf_mul0 p1 p2); case: sr_cancel => s c3 /= Hs.
  case/holds0_cat => /IH1 -> /holds0_cat [/IH2 -> /Hs ->].
  by rewrite nf_mul0_sound.
- move: IH1; case: (normcs rels e1) => p c1 /= IH1.
  have := @sr_cancel_sound (nf_pow0 p k); case: sr_cancel => s c3 /= Hs.
  case/holds0_cat => /IH1 -> /Hs ->.
  by rewrite nf_pow0_sound.
move: IH1; case: (normcs rels e1) => p c1 /= IH1.
have := @sr_cancel_sound (nf_inv0 p); case: sr_cancel => s c3 /= Hs.
case/holds0_cat => /IH1 -> /Hs ->.
by rewrite nf_inv0_sound.
Qed.

End SymSound.

(* The decision theorem: any root function rt, the relations as hypotheses *)
Theorem radcan_eq_cond_sym (F : numFieldType) (rt : nat -> F -> F)
    (env : seq F) rels e1 e2 cs :
  radcan_check_sym rels e1 e2 = Some cs -> rels_hold rt env rels ->
  all_conds_gen rt env cs -> rinterp_gen rt env e1 = rinterp_gen rt env e2.
Proof.
rewrite /radcan_check_sym => + Hr.
have := @normcs_sound F rt env rels Hr e1.
case: (normcs rels e1) => p1 c1 /= H1.
have := @normcs_sound F rt env rels Hr e2.
case: (normcs rels e2) => p2 c2 /= H2.
case: ifP => // /(nf_eqb_eq0 rt env) Hp [<-].
move=> /all_conds_genP /holds0_dedup /holds0_cat [/H1 -> /H2 ->].
by rewrite Hp.
Qed.

Theorem radcan_eq_sym (F : numFieldType) (rt : nat -> F -> F)
    (env : seq F) rels e1 e2 :
  radcan_check_sym rels e1 e2 = Some [::] -> rels_hold rt env rels ->
  rinterp_gen rt env e1 = rinterp_gen rt env e2.
Proof. by move=> H Hr; apply: (radcan_eq_cond_sym H Hr). Qed.
