(******************************************************************************)
(* OmegaPass: explicit values of the small roots of unity (milestone Omega2), *)
(* as a syntactic pre-pass run before the neg-mode checker.                   *)
(* The values of omega_n = wroot w n, n = 3, 4, 6, 12, in square roots and    *)
(* omega_2 are the record smallroot w (OmegaRoot.v).                          *)
(*   omega_expr n     == Some (the explicit value of omega_n) as an rexpr     *)
(*                       (n = 3, 4, 6, 12), omega_2 written 2.-root (-1)      *)
(*   omega_root n a   == (e, cs): the rewriting of RRootE n a; omega_frac for *)
(*                       a fraction with a variable, otherwise a constant     *)
(*                       radicand - p / d < 0 gives n.-root (p / d) * omega_n *)
(*                       (checked by radcan_check, no condition); a radicand  *)
(*                       whose last monomial has a negative coefficient gives *)
(*                       n.-root (- a) * omega_n under cs = [:: 0 <= - a]     *)
(*   omega_frac n om a p q == the rewriting of RRootE n a for a fraction a =  *)
(*                       p / q with a variable (Frac's nd), any n, om the     *)
(*                       value of omega_n: the signs are read on p and q apart*)
(*                       (neg_look: last monomial negative); p negative       *)
(*                       gives n.-root (- p / q) * omega_n under 0 <= - p,    *)
(*                       0 <= q (the conditions frac_split then repeats),     *)
(*                       q negative symmetrically, both negative give         *)
(*                       n.-root (- p / - q) with no condition                *)
(*   omega_rw e       == (e', cs): every RRootE n a of e (innermost first)    *)
(*                       rewritten by omega_root                              *)
(*   omega_rw_sound   : smallroot w -> omega_rw e = (e', cs) ->               *)
(*                      all_conds r env cs -> rinterp e' = rinterp e          *)
(*   radcan_eq_omega, radcan_eq_omega_refined == decision theorems:           *)
(*                       omega_rw on both sides, then radcan_check_neg,       *)
(*                       conditions cs1 ++ cs2 ++ cs                          *)
(* On C: w = rootC_negroot C, the record is rootC_smallroot C (OmegaC.v).     *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts Syntax Radcan Refine Frac.
From Radcan Require Import OmegaRoot.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(* The pre-pass *)

Definition omega2_e : rexpr := RRootE 2 (RCst (Zneg 1)).

Definition omega_expr (n : positive) : option rexpr :=
  if Pos.eqb n 3 then
    Some (RMul (RAdd (RCst 1) (RMul (RRoot 2 3) omega2_e)) (RInv (RCst 2)))
  else if Pos.eqb n 4 then
    Some (RMul (RMul (RRoot 2 2) (RInv (RCst 2))) (RAdd (RCst 1) omega2_e))
  else if Pos.eqb n 6 then
    Some (RMul (RAdd (RRoot 2 3) omega2_e) (RInv (RCst 2)))
  else if Pos.eqb n 12 then
    Some (RMul (RAdd (RAdd (RRoot 2 6) (RRoot 2 2))
                     (RMul (RSub (RRoot 2 6) (RRoot 2 2)) omega2_e))
               (RInv (RCst 4)))
  else None.

(* n.-root (p / d) *)
Definition qroot (n p d : positive) : rexpr :=
  if Pos.eqb d 1 then RRoot n p
  else RRootE n (RMul (RCst (Zpos p)) (RInv (RCst (Zpos d)))).

(* candidate: the radicand is the constant - p / d (checked afterwards) *)
Definition neg_const (p : nf) : option (positive * positive) :=
  if const_of p is Some c then
    let q := ZNum.c_to_Q c in
    if QArith_base.Qnum q is Zneg pp then Some (pp, QArith_base.Qden q)
    else None
  else None.

(* the last monomial of the normal form has a negative coefficient *)
Definition last_neg (p : nf) : bool :=
  if p is t :: p' then
    Z.ltb (QArith_base.Qnum (ZNum.c_to_Q (last t p').1)) 0
  else false.

(* - a, cancelling an opposite or the sign of a literal *)
Definition oneg (a : rexpr) : rexpr :=
  match a with
  | ROpp b => b
  | RCst (Zneg p) => RCst (Zpos p)
  | _ => ROpp a
  end.

(* a looks negative: its normal form has a last negative coefficient *)
Definition neg_look (a : rexpr) : bool := last_neg (radcan_nf MStd a a).1.1.

(* omega_n, explicit for n = 2, 3, 4, 6, 12 *)
Definition omega_val (n : positive) : rexpr :=
  if omega_expr n is Some om then om else RRootE n (RCst (Zneg 1)).

(* n.-root a with a = p / q: the signs of p and q are flipped separately *)
Definition omega_frac (n : positive) (om a p q : rexpr) :
    rexpr * seq cond :=
  match neg_look p, neg_look q with
  | true, true => (RRootE n (RMul (oneg p) (RInv (oneg q))), [::])
  | true, false =>
      (RMul (RRootE n (RMul (oneg p) (RInv q))) om, fge0 (oneg p) ++ fge0 q)
  | false, true =>
      (RMul (RRootE n (RMul p (RInv (oneg q)))) om, fge0 p ++ fge0 (oneg q))
  | false, false => (RRootE n a, [::])
  end.

Definition omega_root (n : positive) (a : rexpr) : rexpr * seq cond :=
  let: (p, q, f) := nd a in
  if f && has_var a then omega_frac n (omega_val n) a p q else
  if omega_expr n is Some om then
    let p := (radcan_nf MStd a a).1.1 in
    if neg_const p is Some (pp, d) then
      if radcan_check a (RMul (RCst (Zneg pp)) (RInv (RCst (Zpos d))))
        is Some [::] then
        (if Pos.eqb pp 1 && Pos.eqb d 1 then om
         else RMul (qroot n pp d) om, [::])
      else (RRootE n a, [::])
    else if last_neg p then (RMul (RRootE n (ROpp a)) om, [:: CGe0 (ROpp a)])
    else (RRootE n a, [::])
  else (RRootE n a, [::]).

Arguments omega_root : simpl never.

Fixpoint omega_rw (e : rexpr) : rexpr * seq cond :=
  match e with
  | RRootE n a =>
    let: (a', c1) := omega_rw a in
    let: (e', c2) := omega_root n a' in (e', c1 ++ c2)
  | RAdd a b =>
    let: (a', c1) := omega_rw a in let: (b', c2) := omega_rw b in
    (RAdd a' b', c1 ++ c2)
  | ROpp a => let: (a', c1) := omega_rw a in (ROpp a', c1)
  | RSub a b =>
    let: (a', c1) := omega_rw a in let: (b', c2) := omega_rw b in
    (RSub a' b', c1 ++ c2)
  | RMul a b =>
    let: (a', c1) := omega_rw a in let: (b', c2) := omega_rw b in
    (RMul a' b', c1 ++ c2)
  | RPow a k => let: (a', c1) := omega_rw a in (RPow a' k, c1)
  | RInv a => let: (a', c1) := omega_rw a in (RInv a', c1)
  | RCst _ | RVar _ | RRoot _ _ => (e, [::])
  end.

(* Soundness *)

Section OmegaSound.

Variables (F : numFieldType) (r : posroot F) (w : negroot r) (env : seq F).
Hypothesis ov : smallroot w.

Local Notation ri := (rinterp r env).

Lemma pos_to_nat_gt0 (n : positive) : (0 < Pos.to_nat n)%N.
Proof. by apply/ssrnat.ltP/Pos2Nat.is_pos. Qed.

Lemma omega2_eE : ri omega2_e = wroot w 2.
Proof. by rewrite /= /pos2F mulr1n wrootE. Qed.

Lemma omega_exprE n om : omega_expr n = Some om ->
  ri om = wroot w (Pos.to_nat n).
Proof.
rewrite /omega_expr.
case: Pos.eqb_spec => [-> [<-]|_].
  by rewrite /= (wroot3 ov) -omega2_eE.
case: Pos.eqb_spec => [-> [<-]|_].
  by rewrite /= (wroot4 ov) -omega2_eE.
case: Pos.eqb_spec => [-> [<-]|_].
  by rewrite /= (wroot6 ov) -omega2_eE.
case: Pos.eqb_spec => [-> [<-]|//].
by rewrite /= (wroot12 ov) -omega2_eE.
Qed.

Lemma qrootE n p d :
  ri (qroot n p d) = proot r (Pos.to_nat n) (pos2F F p / pos2F F d).
Proof.
rewrite /qroot; case: (Pos.eqb_spec d 1) => [->|_] //=.
by rewrite /pos2F /= mulr1n invr1 mulr1.
Qed.

Lemma onegE a : ri (oneg a) = - ri a.
Proof. by case: a => //= [[|p|p]|e] //=; rewrite opprK. Qed.

Lemma omega_valE n : ri (omega_val n) = wroot w (Pos.to_nat n).
Proof.
rewrite /omega_val; case E: (omega_expr n) => [om|]; first exact: omega_exprE.
by rewrite /= /pos2F mulr1n wrootE // pos_to_nat_gt0.
Qed.

Lemma omega_fracE n om a p q e cs :
  ri om = wroot w (Pos.to_nat n) -> ri a = ri p * (ri q)^-1 ->
  omega_frac n om a p q = (e, cs) -> all_conds_gen (proot r) env cs ->
  ri e = proot r (Pos.to_nat n) (ri a).
Proof.
have n0 := pos_to_nat_gt0 n.
move=> Om Ha; rewrite /omega_frac.
case: (neg_look p); case: (neg_look q) => -[<- <-] //=.
- by rewrite !onegE invrN mulrNN Ha.
- case/all_conds_gen_cat => /fge0P hp /fge0P hq.
  rewrite Om -(prootNw w n0) ?mulr_ge0 ?invr_ge0 //.
  by rewrite onegE mulNr opprK Ha.
case/all_conds_gen_cat => /fge0P hp /fge0P hq.
rewrite Om -(prootNw w n0) ?mulr_ge0 ?invr_ge0 //.
by rewrite onegE invrN mulrN opprK Ha.
Qed.

Lemma omega_rootE n a e cs : omega_root n a = (e, cs) ->
  all_conds_gen (proot r) env cs -> ri e = proot r (Pos.to_nat n) (ri a).
Proof.
have n0 := pos_to_nat_gt0 n.
rewrite /omega_root; have := ndE (proot r) env a.
case: (nd a) => [[p0 q0] f] /= Hnd.
case: ifP => _; first by apply: omega_fracE Hnd; rewrite ?omega_valE.
case Eo: (omega_expr n) => [om|]; last by case=> <-.
have Om := omega_exprE Eo.
case: (neg_const _) => [[pp d]|].
  case E: (radcan_check _ _) => [[|c cs']|]; try by case=> <-.
  have /= Ha := radcan_eq_cond (r := r) (env := env) E I.
  have pd0 : 0 <= pos2F F pp / pos2F F d.
    by rewrite divr_ge0 ?pos2F_ge0.
  rewrite Ha mulNr (prootNw w n0 pd0) -Om -qrootE.
  case: ifP => [|_]; last by case=> <-.
  case: pp {E Ha pd0} => [p|p|] //; case: d => [q|q|] // _ [<- _] _.
  by rewrite /qroot /= /pos2F mulr1n proot_1 // mul1r.
case: (last_neg _); last by case=> <-.
case=> <- <- /= h.
by rewrite -{2}[ri a]opprK (prootNw w n0 h) Om.
Qed.

Lemma omega_rw_sound_gen e :
  all_conds_gen (proot r) env (omega_rw e).2 -> ri (omega_rw e).1 = ri e.
Proof.
elim: e => //= [n e1 IH1|e1 IH1 e2 IH2|e1 IH1|e1 IH1 e2 IH2
  |e1 IH1 e2 IH2|e1 IH1 k|e1 IH1].
- case: (omega_rw e1) IH1 => a' ca /= IH1.
  case E: (omega_root n a') => [e' ce] /= /all_conds_gen_cat [/IH1 <- h].
  exact: omega_rootE E h.
- case: (omega_rw e1) IH1 => e1' c1 /= IH1.
  case: (omega_rw e2) IH2 => e2' c2 /= IH2.
  by case/all_conds_gen_cat => /IH1 -> /IH2 ->.
- by case: (omega_rw e1) IH1 => e1' c1 /= IH1 /IH1 ->.
- case: (omega_rw e1) IH1 => e1' c1 /= IH1.
  case: (omega_rw e2) IH2 => e2' c2 /= IH2.
  by case/all_conds_gen_cat => /IH1 -> /IH2 ->.
- case: (omega_rw e1) IH1 => e1' c1 /= IH1.
  case: (omega_rw e2) IH2 => e2' c2 /= IH2.
  by case/all_conds_gen_cat => /IH1 -> /IH2 ->.
- by case: (omega_rw e1) IH1 => e1' c1 /= IH1 /IH1 ->.
by case: (omega_rw e1) IH1 => e1' c1 /= IH1 /IH1 ->.
Qed.

Theorem omega_rw_sound e e' cs :
  omega_rw e = (e', cs) -> all_conds r env cs -> ri e' = ri e.
Proof.
move=> E /all_conds_bridge; rewrite -[cs]/(e', cs).2 -[e']/(e', cs).1 -E.
exact: omega_rw_sound_gen.
Qed.

Theorem radcan_eq_omega e1 e2 e1' e2' cs1 cs2 cs :
  omega_rw e1 = (e1', cs1) -> omega_rw e2 = (e2', cs2) ->
  radcan_check_neg e1' e2' = Some cs -> all_conds r env (cs1 ++ cs2 ++ cs) ->
  ri e1 = ri e2.
Proof.
move=> E1 E2 H /all_conds_cat[h1 /all_conds_cat[h2 h]].
rewrite -(omega_rw_sound E1 h1) -(omega_rw_sound E2 h2).
exact: (radcan_eq_cond_neg w H h).
Qed.

Theorem radcan_eq_omega_refined e1 e2 e1' e2' cs1 cs2 cs rcs :
  omega_rw e1 = (e1', cs1) -> omega_rw e2 = (e2', cs2) ->
  radcan_check_neg e1' e2' = Some cs -> refine (cs1 ++ cs2 ++ cs) = rcs ->
  all_rconds F (proot r) env rcs -> ri e1 = ri e2.
Proof.
move=> E1 E2 H Hr Hc; apply: radcan_eq_omega E1 E2 H _.
by apply: all_conds_bridge_back; apply: refine_sound; rewrite Hr.
Qed.

End OmegaSound.
