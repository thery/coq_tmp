(******************************************************************************)
(* Frac: roots of fractions, the paper's rule (i): (P / Q)^(1/n) is           *)
(* P^(1/n) / Q^(1/n), as a syntactic pre-pass run before the checkers.        *)
(*   nd e          == (P, Q, f): e = P * Q^-1 read off the products, powers,  *)
(*                    opposites and inverses at the top of e; f is true iff   *)
(*                    an inverse was met (e is a fraction)                    *)
(*   frac_split b e == (e', cs): every RRootE n a of e (innermost first)      *)
(*                    whose radicand a = P / Q is a fraction with a variable  *)
(*                    becomes RRootE n P * (RRootE n Q)^-1, under the         *)
(*                    conditions cs = 0 <= P, 0 <= Q (positive literals P, Q  *)
(*                    give no condition); with b = true (real mode) odd       *)
(*                    roots split without condition                           *)
(*   frac_split_sound : all_conds_gen (proot r) env cs ->                     *)
(*                    rinterp r env e = rinterp r env e' (b = false)          *)
(*   frac_split_sound_real : the same for b = true, given a realroot r        *)
(*   radcan_eq_frac, radcan_eq_frac_refined (+ _odd, _neg, _real) ==          *)
(*                    decision theorems: frac_split on both sides, then the   *)
(*                    checker of the mode, conditions cs1 ++ cs2 ++ cs        *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts RealRoot Syntax Radcan Refine.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(* The pre-pass *)

Fixpoint has_var (e : rexpr) : bool :=
  match e with
  | RVar _ => true
  | RCst _ | RRoot _ _ => false
  | RRootE _ e1 | ROpp e1 | RPow e1 _ | RInv e1 => has_var e1
  | RAdd e1 e2 | RSub e1 e2 | RMul e1 e2 => has_var e1 || has_var e2
  end.

Definition fone : rexpr := RCst (Zpos 1).

(* product, dropping the factors 1 *)
Definition fmul (a b : rexpr) : rexpr :=
  match a, b with
  | RCst (Zpos 1), _ => b
  | _, RCst (Zpos 1) => a
  | _, _ => RMul a b
  end.

Fixpoint nd (e : rexpr) : rexpr * rexpr * bool :=
  match e with
  | RMul a b =>
      let: (pa, qa, fa) := nd a in
      let: (pb, qb, fb) := nd b in
      if fa || fb then (fmul pa pb, fmul qa qb, true) else (e, fone, false)
  | RInv a => let: (pa, qa, _) := nd a in (qa, pa, true)
  | RPow a k =>
      let: (pa, qa, fa) := nd a in
      if fa then (RPow pa k, RPow qa k, true) else (e, fone, false)
  | ROpp a =>
      let: (pa, qa, fa) := nd a in
      if fa then (ROpp pa, qa, true) else (e, fone, false)
  | _ => (e, fone, false)
  end.

(* n-th root of a, a numeral radicand as RRoot *)
Definition froot (n : positive) (a : rexpr) : rexpr :=
  if a is RCst (Zpos p) then RRoot n p else RRootE n a.

(* 0 <= a, nothing for a positive literal *)
Definition fge0 (a : rexpr) : seq cond :=
  if a is RCst (Zpos _) then [::] else [:: CGe0 a].

Definition split_root (b : bool) (n : positive) (a : rexpr) :
    rexpr * seq cond :=
  let: (p, q, f) := nd a in
  if f && has_var a then
    (RMul (froot n p) (RInv (froot n q)),
     if b && odd (Pos.to_nat n) then [::] else fge0 p ++ fge0 q)
  else (RRootE n a, [::]).

Fixpoint frac_split (b : bool) (e : rexpr) : rexpr * seq cond :=
  match e with
  | RRootE n a =>
      let: (a', ca) := frac_split b a in
      let: (e', ce) := split_root b n a' in (e', ca ++ ce)
  | RAdd e1 e2 =>
      let: (e1', c1) := frac_split b e1 in
      let: (e2', c2) := frac_split b e2 in (RAdd e1' e2', c1 ++ c2)
  | RSub e1 e2 =>
      let: (e1', c1) := frac_split b e1 in
      let: (e2', c2) := frac_split b e2 in (RSub e1' e2', c1 ++ c2)
  | RMul e1 e2 =>
      let: (e1', c1) := frac_split b e1 in
      let: (e2', c2) := frac_split b e2 in (RMul e1' e2', c1 ++ c2)
  | ROpp e1 => let: (e1', c1) := frac_split b e1 in (ROpp e1', c1)
  | RPow e1 k => let: (e1', c1) := frac_split b e1 in (RPow e1' k, c1)
  | RInv e1 => let: (e1', c1) := frac_split b e1 in (RInv e1', c1)
  | _ => (e, [::])
  end.

(* Soundness *)

Section Sound.

Variables (F : numFieldType) (rt : nat -> F -> F) (env : seq F).

Local Notation ri := (rinterp_gen rt env).

Lemma all_conds_genP cs :
  all_conds_gen rt env cs <->
  forall c, List.In c cs -> cond_interp_gen rt env c.
Proof.
elim: cs => [|c cs IH] //=; case: cs IH => [|c' cs] IH.
  by split=> [h c0 [<-|]|h] //; apply: h; left.
split=> [[h1 /IH h2] c0 [<-|/h2]|h] //.
by split; [apply: h; left|apply/IH => c0 hc; apply: h; right].
Qed.

Lemma all_conds_gen_cat cs1 cs2 :
  all_conds_gen rt env (cs1 ++ cs2) <->
  all_conds_gen rt env cs1 /\ all_conds_gen rt env cs2.
Proof.
rewrite !all_conds_genP; split=> [h|[h1 h2] c].
  by split=> c hc; apply: h; apply: List.in_or_app; [left|right].
by move=> /(List.in_app_or cs1 cs2 c)[];[apply: h1|apply: h2].
Qed.

Lemma fmulE a b : ri (fmul a b) = ri a * ri b.
Proof.
have p1 : pos2F F 1 = 1 by rewrite /pos2F mulr1n.
by rewrite /fmul; case: a => [[|[p|p|]|]|||||||||] => *;
  case: b => [[|[q|q|]|]|||||||||] => * /=; rewrite ?p1 ?mulr1 ?mul1r.
Qed.

Lemma ndE e : ri e = ri (nd e).1.1 * (ri (nd e).1.2)^-1.
Proof.
have one : ri fone = 1 by rewrite /= /pos2F mulr1n.
elim: e => [z|i|n p|n e1 IH1|e1 IH1 e2 IH2|e1 IH1|e1 IH1 e2 IH2|e1 IH1 e2 IH2
  |e1 IH1 k|e1 IH1] /=; rewrite ?one ?invr1 ?mulr1 //.
all: try (case: (nd e1) IH1 => [[p q] f] /= IH1).
all: try (case: (nd e2) IH2 => [[p2 q2] f2] /= IH2).
- by case: f => /=; rewrite ?one ?invr1 ?mulr1 // IH1 mulNr.
- case: (f || f2) => /=; rewrite ?one ?invr1 ?mulr1 //.
  by rewrite IH1 IH2 !fmulE invfM mulrACA.
- by case: f => /=; rewrite ?one ?invr1 ?mulr1 // IH1 exprMn exprVn.
by rewrite IH1 invfM invrK mulrC.
Qed.

Lemma frootE n a : ri (froot n a) = rt (Pos.to_nat n) (ri a).
Proof. by case: a => // [[]]. Qed.

Lemma fge0P a : all_conds_gen rt env (fge0 a) -> 0 <= ri a.
Proof. by case: a => //= [[]] //= p _; apply: ler0n. Qed.

End Sound.

Section RootSound.

Variables (F : numFieldType) (r : posroot F) (env : seq F).

Local Notation ri := (rinterp r env).

Lemma proot_oddV (rl : realroot r) n a : odd n ->
  proot r n a^-1 = (proot r n a)^-1.
Proof.
move=> On; have n0 : (0 < n)%N by case: n On.
have [a' a0 [->|->]] := realroot_sign rl a; first by rewrite prootV.
by rewrite invrN !(prootN (realroot_odd rl)) // prootV // invrN.
Qed.

Lemma split_rootE (b : bool) n a :
  (b -> realroot r) ->
  all_conds_gen (proot r) env (split_root b n a).2 ->
  proot r (Pos.to_nat n) (ri a) = ri (split_root b n a).1.
Proof.
move=> hb; rewrite /split_root; have := ndE (proot r) env a.
case: (nd a) => [[p q] f] /= E; case: ifP => //= _.
rewrite E !frootE; case: ifP => [/andP[/hb rl On] _|_].
  by rewrite (proot_oddM rl) // (proot_oddV rl).
case/all_conds_gen_cat => /fge0P hp /fge0P hq.
have n0 : (0 < Pos.to_nat n)%N by apply/ssrnat.ltP/Pos2Nat.is_pos.
by rewrite prootM ?invr_ge0 // prootV.
Qed.

Lemma frac_split_sound_gen (b : bool) e :
  (b -> realroot r) ->
  all_conds_gen (proot r) env (frac_split b e).2 ->
  ri e = ri (frac_split b e).1.
Proof.
move=> hb; elim: e => //= [n e1 IH1|e1 IH1 e2 IH2|e1 IH1|e1 IH1 e2 IH2
  |e1 IH1 e2 IH2|e1 IH1 k|e1 IH1].
- case: (frac_split b e1) IH1 => a' ca /= IH1.
  case E: (split_root b n a') => [e' ce] /= /all_conds_gen_cat [/IH1 -> h].
  by move: (@split_rootE b n a' hb); rewrite E; apply.
- case: (frac_split b e1) IH1 => e1' c1 /= IH1.
  case: (frac_split b e2) IH2 => e2' c2 /= IH2.
  by case/all_conds_gen_cat => /IH1 -> /IH2 ->.
- by case: (frac_split b e1) IH1 => e1' c1 /= IH1 /IH1 ->.
- case: (frac_split b e1) IH1 => e1' c1 /= IH1.
  case: (frac_split b e2) IH2 => e2' c2 /= IH2.
  by case/all_conds_gen_cat => /IH1 -> /IH2 ->.
- case: (frac_split b e1) IH1 => e1' c1 /= IH1.
  case: (frac_split b e2) IH2 => e2' c2 /= IH2.
  by case/all_conds_gen_cat => /IH1 -> /IH2 ->.
- by case: (frac_split b e1) IH1 => e1' c1 /= IH1 /IH1 ->.
by case: (frac_split b e1) IH1 => e1' c1 /= IH1 /IH1 ->.
Qed.

Theorem frac_split_sound e e' cs :
  frac_split false e = (e', cs) -> all_conds r env cs -> ri e = ri e'.
Proof.
move=> E /all_conds_bridge; rewrite -[cs]/(e', cs).2 -[e']/(e', cs).1 -E.
exact: frac_split_sound_gen.
Qed.

Theorem frac_split_sound_real (rl : realroot r) e e' cs :
  frac_split true e = (e', cs) -> all_conds r env cs -> ri e = ri e'.
Proof.
move=> E /all_conds_bridge; rewrite -[cs]/(e', cs).2 -[e']/(e', cs).1 -E.
exact: frac_split_sound_gen.
Qed.

End RootSound.

(* Decision theorems: frac_split on both sides, then the checker *)

Section Decide.

Variables (F : numFieldType) (r : posroot F) (env : seq F).

Lemma all_conds_cat cs1 cs2 :
  all_conds r env (cs1 ++ cs2) <-> all_conds r env cs1 /\ all_conds r env cs2.
Proof.
split=> [/all_conds_bridge/all_conds_gen_cat[h1 h2]|[h1 h2]].
  by split; apply: all_conds_bridge_back.
apply: all_conds_bridge_back; apply/all_conds_gen_cat.
by split; apply: all_conds_bridge.
Qed.

Lemma frac_eq_gen (b : bool) (chk : rexpr -> rexpr -> option (seq cond))
    e1 e2 e1' e2' cs1 cs2 cs :
  (b -> realroot r) ->
  (forall e1 e2 cs, chk e1 e2 = Some cs -> all_conds r env cs ->
     rinterp r env e1 = rinterp r env e2) ->
  frac_split b e1 = (e1', cs1) -> frac_split b e2 = (e2', cs2) ->
  chk e1' e2' = Some cs -> all_conds r env (cs1 ++ cs2 ++ cs) ->
  rinterp r env e1 = rinterp r env e2.
Proof.
move=> hb hchk E1 E2 H /all_conds_cat[h1 /all_conds_cat[h2 h]].
have S1 := @frac_split_sound_gen F r env b e1 hb.
have S2 := @frac_split_sound_gen F r env b e2 hb.
rewrite E1 E2 /= in S1 S2.
rewrite S1 ?S2; try exact: all_conds_bridge.
exact: hchk H h.
Qed.

Theorem radcan_eq_frac e1 e2 e1' e2' cs1 cs2 cs :
  frac_split false e1 = (e1', cs1) -> frac_split false e2 = (e2', cs2) ->
  radcan_check e1' e2' = Some cs -> all_conds r env (cs1 ++ cs2 ++ cs) ->
  rinterp r env e1 = rinterp r env e2.
Proof.
move=> E1 E2 H Hc; apply: (frac_eq_gen _ _ E1 E2 H Hc) => // e3 e4 cs3.
exact: radcan_eq_cond.
Qed.

Theorem radcan_eq_frac_refined e1 e2 e1' e2' cs1 cs2 cs rcs :
  frac_split false e1 = (e1', cs1) -> frac_split false e2 = (e2', cs2) ->
  radcan_check e1' e2' = Some cs -> refine (cs1 ++ cs2 ++ cs) = rcs ->
  all_rconds F (proot r) env rcs -> rinterp r env e1 = rinterp r env e2.
Proof.
move=> E1 E2 H Hr Hc; apply: radcan_eq_frac E1 E2 H _.
by apply: all_conds_bridge_back; apply: refine_sound; rewrite Hr.
Qed.

Theorem radcan_eq_frac_odd (o : oddroot r) e1 e2 e1' e2' cs1 cs2 cs :
  frac_split false e1 = (e1', cs1) -> frac_split false e2 = (e2', cs2) ->
  radcan_check_odd e1' e2' = Some cs -> all_conds r env (cs1 ++ cs2 ++ cs) ->
  rinterp r env e1 = rinterp r env e2.
Proof.
move=> E1 E2 H Hc; apply: (frac_eq_gen _ _ E1 E2 H Hc) => // e3 e4 cs3.
exact: (radcan_eq_cond_odd o).
Qed.

Theorem radcan_eq_frac_refined_odd (o : oddroot r) e1 e2 e1' e2' cs1 cs2 cs
    rcs :
  frac_split false e1 = (e1', cs1) -> frac_split false e2 = (e2', cs2) ->
  radcan_check_odd e1' e2' = Some cs -> refine (cs1 ++ cs2 ++ cs) = rcs ->
  all_rconds F (proot r) env rcs -> rinterp r env e1 = rinterp r env e2.
Proof.
move=> E1 E2 H Hr Hc; apply: (radcan_eq_frac_odd o) E1 E2 H _.
by apply: all_conds_bridge_back; apply: refine_sound; rewrite Hr.
Qed.

Theorem radcan_eq_frac_neg (w : negroot r) e1 e2 e1' e2' cs1 cs2 cs :
  frac_split false e1 = (e1', cs1) -> frac_split false e2 = (e2', cs2) ->
  radcan_check_neg e1' e2' = Some cs -> all_conds r env (cs1 ++ cs2 ++ cs) ->
  rinterp r env e1 = rinterp r env e2.
Proof.
move=> E1 E2 H Hc; apply: (frac_eq_gen _ _ E1 E2 H Hc) => // e3 e4 cs3.
exact: (radcan_eq_cond_neg w).
Qed.

Theorem radcan_eq_frac_refined_neg (w : negroot r) e1 e2 e1' e2' cs1 cs2 cs
    rcs :
  frac_split false e1 = (e1', cs1) -> frac_split false e2 = (e2', cs2) ->
  radcan_check_neg e1' e2' = Some cs -> refine (cs1 ++ cs2 ++ cs) = rcs ->
  all_rconds F (proot r) env rcs -> rinterp r env e1 = rinterp r env e2.
Proof.
move=> E1 E2 H Hr Hc; apply: (radcan_eq_frac_neg w) E1 E2 H _.
by apply: all_conds_bridge_back; apply: refine_sound; rewrite Hr.
Qed.

(* real mode: odd roots of fractions split with no condition *)
Theorem radcan_eq_frac_real (rl : realroot r) e1 e2 e1' e2' cs1 cs2 cs :
  frac_split true e1 = (e1', cs1) -> frac_split true e2 = (e2', cs2) ->
  radcan_check_real e1' e2' = Some cs -> all_conds r env (cs1 ++ cs2 ++ cs) ->
  rinterp r env e1 = rinterp r env e2.
Proof.
move=> E1 E2 H Hc.
apply: (frac_eq_gen (fun _ => rl) _ E1 E2 H Hc) => // e3 e4 cs3.
exact: (radcan_eq_cond_real rl).
Qed.

Theorem radcan_eq_frac_refined_real (rl : realroot r) e1 e2 e1' e2' cs1 cs2
    cs rcs :
  frac_split true e1 = (e1', cs1) -> frac_split true e2 = (e2', cs2) ->
  radcan_check_real e1' e2' = Some cs -> refine (cs1 ++ cs2 ++ cs) = rcs ->
  all_rconds F (proot r) env rcs -> rinterp r env e1 = rinterp r env e2.
Proof.
move=> E1 E2 H Hr Hc; apply: (radcan_eq_frac_real rl) E1 E2 H _.
by apply: all_conds_bridge_back; apply: refine_sound; rewrite Hr.
Qed.

End Decide.
