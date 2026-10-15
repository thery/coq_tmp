(******************************************************************************)
(* Simplify: normal forms printed back as readable expressions, for the       *)
(* tactic radcan_simplify (SimplifyTac.v).                                    *)
(*   pp_nf rp p       == the normal form p as an rexpr: terms sorted (higher  *)
(*                       powers of the first atoms first, constant last),     *)
(*                       negative terms as subtractions, no coefficient 1,    *)
(*                       rational coefficients as a / q, inverse atoms as a   *)
(*                       denominator, terms with the same inverse atoms over  *)
(*                       a common denominator; rp: proot n a ^+ k printed as  *)
(*                       proot n (a ^+ k); |B| = proot 2 (B ^+ 2) kept        *)
(*   simpl_mk rp e (rt, m) == printed normal form of e in mode m (rt:         *)
(*                       rationalise denominators), normc0 if root-free       *)
(*   simpl_pref chk ms e == Some (e', cs): e' the first candidate (modes ms,  *)
(*                       rationalised first) proved equal to e by the checker *)
(*                       chk under cs; then with roots of powers (rp) if      *)
(*                       they add no condition                                *)
(*   radcan_simpl, radcan_simpl_odd, radcan_simpl_neg, radcan_simpl_real ==   *)
(*                    simpl_pref with                                         *)
(*                       radcan_check, radcan_check_odd, radcan_check_neg,    *)
(*                       radcan_check_real (modes MRealA, MReal)              *)
(*   radcan_simpl_sound, ..._odd, ..._neg, ..._real, radcan_simpl_sound0 ==   *)
(*                       rinterp r env e = rinterp r env e' under the refined *)
(*                       conditions (Refine.v); radcan_simpl_cond*: raw ones  *)
(* The printer needs no proof: e = e' is proved by the decision procedure,    *)
(* which normalises e' again (stability of the printed form).                 *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt ZArith QArith_base.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot Syntax Backend Radcan Refine OddRoot.
From Radcan Require Import NegRootC RealRoot AbsRoot.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Printing                                                                   *)

(* left-nested products: a * b * c                                            *)
Definition lprod (l : seq rexpr) : rexpr :=
  if l is a :: l' then foldl RMul a l' else RCst 1.

Definition pp_pow (e : rexpr) (k : nat) : rexpr :=
  if k == 1%N then e else RPow e k.

Definition is_inv (a : atom) : bool := if a is AInv _ then true else false.

Section PrettyNF.

(* printer of the expressions inside atoms *)
Variable inner : rexpr -> rexpr.
(* rp: powers of roots printed as roots of powers *)
Variable rp : bool.

(* |B| = proot 2 (B ^+ 2) (real mode) keeps its form, B printed alone *)
Definition pp_atom (a : atom) (k : nat) : rexpr :=
  match a with
  | AVar i => pp_pow (RVar i) k
  | AInv e => pp_pow (inner e) k
  | ARoot 2 (RPow b 2) => pp_pow (RRootE 2 (RPow (inner b) 2)) k
  | ARoot n e => if rp then RRootE n (pp_pow (inner e) k)
                 else pp_pow (RRootE n (inner e)) k
  end.

Definition pp_fct (f : fct) : rexpr :=
  let: (b, n, k) := f in
  if rp then RRoot (Pos.of_nat n) (Pos.pow b (Pos.of_nat k))
  else pp_pow (RRoot (Pos.of_nat n) b) k.

(* numerator factors and inverse atoms of a term *)
Definition num_fs (t : coef * key) : seq rexpr :=
  [seq pp_atom ak.1 ak.2 | ak <- t.2.1 & ~~ is_inv ak.1] ++ map pp_fct t.2.2.

Definition den_v (t : coef * key) : vmono := [seq ak <- t.2.1 | is_inv ak.1].

Definition den_fs (v : vmono) : seq rexpr := [seq pp_atom ak.1 ak.2 | ak <- v].

(* a * fs (a > 0) and n / ds *)
Definition pp_mono (a : Z) (fs : seq rexpr) : rexpr :=
  if fs is [::] then RCst a
  else if Z.eqb a 1 then lprod fs else lprod (RCst a :: fs).

Definition pp_div (n : rexpr) (ds : seq rexpr) : rexpr :=
  if ds is [::] then n else RMul n (RInv (lprod ds)).

(* signed sum; a leading negative term is exchanged with the first positive
   one: 1 - x, not - x + 1 *)
Definition pp_lead (ts : seq (bool * rexpr)) : seq (bool * rexpr) :=
  if ts is (true, _) :: _ then
    let i := find (fun t => ~~ t.1) ts in
    if (i < size ts)%N then
      nth (false, RCst 0) ts i :: take i ts ++ drop i.+1 ts
    else ts
  else ts.

Definition pp_sum (ts : seq (bool * rexpr)) : rexpr :=
  match pp_lead ts with
  | [::] => RCst 0
  | (s, x) :: ts' =>
      foldl (fun acc t => if t.1 then RSub acc t.2 else RAdd acc t.2)
            (if s then ROpp x else x) ts'
  end.

Definition t_q (t : coef * key) : Q := ZNum.c_to_Q t.1.

Definition t_neg (t : coef * key) : bool := Z.ltb (Qnum (t_q t)) 0.

(* one term, alone: (negative, |t|) *)
Definition pp_term (t : coef * key) : bool * rexpr :=
  let q := t_q t in
  let ds := den_fs (den_v t) in
  let ds := if Pos.eqb (Qden q) 1 then ds else RCst (Zpos (Qden q)) :: ds in
  (t_neg t, pp_div (pp_mono (Z.abs (Qnum q)) (num_fs t)) ds).

(* terms with the same inverse atoms v, over a common denominator *)
Definition pp_group (v : vmono) (ts : seq (coef * key)) : bool * rexpr :=
  let d := foldl (fun d t => Z.to_pos (Z.lcm (Zpos d) (Zpos (Qden (t_q t)))))
                 1%positive ts in
  let num t :=
    Z.mul (Z.abs (Qnum (t_q t))) (Z.div (Zpos d) (Zpos (Qden (t_q t)))) in
  let ns := [seq (t_neg t, pp_mono (num t) (num_fs t)) | t <- ts] in
  let s := all (fun t => t.1) ns in
  let ns := if s then [seq (false, t.2) | t <- ns] else ns in
  let ds := den_fs v in
  (s, pp_div (pp_sum ns) (if Pos.eqb d 1 then ds else RCst (Zpos d) :: ds)).

Definition veq (v1 v2 : vmono) : bool := cmp_eqb (vmono_cmp v1 v2).

(* the exponent vectors compared lexicographically, the first atom first *)
Fixpoint vlex (v1 v2 : vmono) : comparison :=
  match v1, v2 with
  | [::], [::] => Eq
  | [::], _ => Lt
  | _, [::] => Gt
  | (a1, k1) :: v1', (a2, k2) :: v2' =>
      match atom_cmp a1 a2 with
      | Lt => Gt
      | Gt => Lt
      | Eq => lex (Nat.compare k1 k2) (vlex v1' v2')
      end
  end.

Definition term_ge (t1 t2 : coef * key) : bool :=
  if lex (vlex t1.2.1 t2.2.1) (mono_cmp t1.2.2 t2.2.2) is Lt then false
  else true.

(* terms sorted (higher powers of the first atoms first, constant last);
   the terms with the same inverse atoms are grouped *)
Definition pp_nf_with (p : nf) : rexpr :=
  let ts := sort term_ge p in
  let vs := foldl (fun acc t => if has (veq (den_v t)) acc then acc
                                else rcons acc (den_v t)) [::] ts in
  let items v :=
    let g := [seq t <- ts | veq (den_v t) v] in
    if v is [::] then map pp_term g
    else if g is [:: t] then [:: pp_term t] else [:: pp_group v g] in
  pp_sum (flatten (map items vs)).

End PrettyNF.

(* inner expressions: structural normal form, printed (fuel: depth) *)
Fixpoint pp_fuel (fuel : nat) (e : rexpr) : rexpr :=
  if fuel is S f then pp_nf_with (pp_fuel f) false (RadcanZ.pnorm e) else e.

Definition pp_nf (rp : bool) (p : nf) : rexpr := pp_nf_with (pp_fuel 20) rp p.

(* Candidate normal forms, computed as in radcan_check_root *)

Definition simpl_nfr (rt : bool) (m : rmode) (e : rexpr) : nf :=
  let hs := neg_hints [:: e] in
  (normcr rt m hs (mk_basis_n rt m hs [:: e]) e).1.

Definition simpl_nf (rt : bool) (m : rmode) (e : rexpr) : nf :=
  simpl_nfr rt m (cb_rw m (const_basis (rconsts m e)) e).

(* candidates: (rationalise, mode); root-free: normc0 *)
Definition simpl_modes (ms : seq rmode) (e : rexpr) : seq (bool * rmode) :=
  if no_root e then [:: (false, MStd)]
  else flatten [seq [:: (true, m); (false, m)] | m <- ms].

Definition simpl_mk (rp : bool) (e : rexpr) (x : bool * rmode) : rexpr :=
  if no_root e then pp_nf rp (normc0 e).1 else pp_nf rp (simpl_nf x.1 x.2 e).

(* the first candidate proved equal to e by the checker chk *)
Fixpoint simpl_with (chk : rexpr -> rexpr -> option (seq cond))
  (e : rexpr) (xs : seq (bool * rmode)) :
  option (bool * rmode * rexpr * seq cond) :=
  if xs is x :: xs' then
    let e' := simpl_mk false e x in
    if chk e e' is Some cs then Some (x, e', cs) else simpl_with chk e xs'
  else None.

Definition cond_sub (cs1 cs2 : seq cond) : bool :=
  all (fun c => has (fun c' => cmp_eqb (cond_cmp c c')) cs2) cs1.

(* then roots of powers, when they need no new condition *)
Definition simpl_pref (chk : rexpr -> rexpr -> option (seq cond))
  (ms : seq rmode) (e : rexpr) : option (rexpr * seq cond) :=
  if simpl_with chk e (simpl_modes ms e) is Some (x, e0, cs0) then
    let e1 := simpl_mk true e x in
    if cmp_eqb (rexpr_cmp e0 e1) then Some (e0, cs0) else
    if chk e e1 is Some cs1 then
      if cond_sub cs1 cs0 then Some (e1, cs1) else Some (e0, cs0)
    else Some (e0, cs0)
  else None.

Lemma simpl_withP chk e xs x e' cs :
  simpl_with chk e xs = Some (x, e', cs) -> chk e e' = Some cs.
Proof.
elim: xs => //= y xs IH; case E : (chk e _) => [cs'|] //.
by case=> _ <- <-.
Qed.

Lemma simpl_prefP chk ms e e' cs :
  simpl_pref chk ms e = Some (e', cs) -> chk e e' = Some cs.
Proof.
rewrite /simpl_pref.
case E0 : simpl_with => [[[x e0] cs0]|] //.
have H0 := simpl_withP E0.
case: ifP => _; first by case=> <- <-.
case E1 : (chk e _) => [cs1|]; last by case=> <- <-.
by case: ifP => _ [<- <-].
Qed.

Definition radcan_simpl (e : rexpr) : option (rexpr * seq cond) :=
  simpl_pref radcan_check [:: MStd] e.

Definition radcan_simpl_odd (e : rexpr) : option (rexpr * seq cond) :=
  simpl_pref radcan_check_odd [:: MOdd] e.

Definition radcan_simpl_neg (e : rexpr) : option (rexpr * seq cond) :=
  simpl_pref radcan_check_neg [:: MNeg; MNegW] e.

Definition radcan_simpl_real (e : rexpr) : option (rexpr * seq cond) :=
  simpl_pref radcan_check_real [:: MRealA; MReal] e.

Local Open Scope ring_scope.

(* Soundness *)

Theorem radcan_simpl_cond (F : numFieldType) (r : posroot F) (env : seq F)
    e e' cs :
  radcan_simpl e = Some (e', cs) -> all_conds r env cs ->
  rinterp r env e = rinterp r env e'.
Proof. by move/simpl_prefP; exact: radcan_eq_cond. Qed.

Theorem radcan_simpl_sound (F : numFieldType) (r : posroot F) (env : seq F)
    e e' cs rcs :
  radcan_simpl e = Some (e', cs) -> refine cs = rcs ->
  all_rconds F (proot r) env rcs -> rinterp r env e = rinterp r env e'.
Proof. by move/simpl_prefP; exact: radcan_eq_refined. Qed.

Theorem radcan_simpl_cond_odd (F : numFieldType) (r : posroot F)
    (o : oddroot r) (env : seq F) e e' cs :
  radcan_simpl_odd e = Some (e', cs) -> all_conds r env cs ->
  rinterp r env e = rinterp r env e'.
Proof. by move/simpl_prefP; exact: radcan_eq_cond_odd. Qed.

Theorem radcan_simpl_sound_odd (F : numFieldType) (r : posroot F)
    (o : oddroot r) (env : seq F) e e' cs rcs :
  radcan_simpl_odd e = Some (e', cs) -> refine cs = rcs ->
  all_rconds F (proot r) env rcs -> rinterp r env e = rinterp r env e'.
Proof. by move/simpl_prefP; exact: radcan_eq_refined_odd. Qed.

Theorem radcan_simpl_cond_neg (F : numFieldType) (r : posroot F)
    (w : negroot r) (env : seq F) e e' cs :
  radcan_simpl_neg e = Some (e', cs) -> all_conds r env cs ->
  rinterp r env e = rinterp r env e'.
Proof. by move/simpl_prefP; exact: radcan_eq_cond_neg. Qed.

Theorem radcan_simpl_sound_neg (F : numFieldType) (r : posroot F)
    (w : negroot r) (env : seq F) e e' cs rcs :
  radcan_simpl_neg e = Some (e', cs) -> refine cs = rcs ->
  all_rconds F (proot r) env rcs -> rinterp r env e = rinterp r env e'.
Proof. by move/simpl_prefP; exact: radcan_eq_refined_neg. Qed.

Theorem radcan_simpl_cond_real (F : numFieldType) (r : posroot F)
    (rl : realroot r) (env : seq F) e e' cs :
  radcan_simpl_real e = Some (e', cs) -> all_conds r env cs ->
  rinterp r env e = rinterp r env e'.
Proof. by move/simpl_prefP; exact: radcan_eq_cond_real. Qed.

Theorem radcan_simpl_sound_real (F : numFieldType) (r : posroot F)
    (rl : realroot r) (env : seq F) e e' cs rcs :
  radcan_simpl_real e = Some (e', cs) -> refine cs = rcs ->
  all_rconds F (proot r) env rcs -> rinterp r env e = rinterp r env e'.
Proof. by move/simpl_prefP; exact: radcan_eq_refined_real. Qed.

(* root-free expressions, no root structure *)
Theorem radcan_simpl_cond0 (F : numFieldType) (env : seq F) e e' cs :
  no_root e -> no_root e' -> radcan_simpl e = Some (e', cs) ->
  all_conds0 env cs -> rinterp0 env e = rinterp0 env e'.
Proof. by move=> n1 n2 /simpl_prefP; exact: radcan_eq_cond0. Qed.

Theorem radcan_simpl_sound0 (F : numFieldType) (env : seq F) e e' cs rcs :
  no_root e -> no_root e' -> radcan_simpl e = Some (e', cs) ->
  refine cs = rcs -> all_rconds F (fun _ _ => 0) env rcs ->
  rinterp0 env e = rinterp0 env e'.
Proof. by move=> n1 n2 /simpl_prefP; exact: radcan_eq_refined0. Qed.

(* rewriting both arguments of a relation *)
Lemma simpl_rel (T : Type) (R : T -> T -> Prop) a a' b b' :
  R a' b' -> a = a' -> b = b' -> R a b.
Proof. by move=> H -> ->. Qed.

Lemma simpl_rel_hyp (T : Type) (R : T -> T -> Prop) a a' b b' :
  a = a' -> b = b' -> R a b -> R a' b'.
Proof. by move=> -> ->. Qed.

Lemma simpl_brel (T : Type) (R : T -> T -> bool) a a' b b' :
  R a' b' -> a = a' -> b = b' -> R a b.
Proof. by move=> H -> ->. Qed.

Lemma simpl_brel_hyp (T : Type) (R : T -> T -> bool) a a' b b' :
  a = a' -> b = b' -> R a b -> R a' b'.
Proof. by move=> -> ->. Qed.
