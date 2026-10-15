(******************************************************************************)
(* Prepass: the composed syntactic pre-pass run when the plain check fails.   *)
(*   prepass_step b om e == omega_rw (OmegaPass.v) when om, then frac_split b *)
(*                    (Frac.v), then denest_rwc (Denest.v); the conditions of *)
(*                    the three passes concatenated (omega_rw first: it turns *)
(*                    n.-root (-8 / x) into n.-root (8 / x) * omega_n, which  *)
(*                    frac_split can then split with 0 <= 8)                  *)
(*   prepass b om fuel e == (e', cs): prepass_step iterated until the         *)
(*                    expression stops changing (that last step adds no       *)
(*                    condition) or fuel runs out                             *)
(*   omega_ok r env  == omega_rw is sound for r and env (omega_ok_small:      *)
(*                    given w : negroot r and smallroot w)                    *)
(*   prepass_sound_gen : (b -> realroot r) -> (om -> omega_ok r env) ->       *)
(*                    all_conds r env cs -> rinterp r env e' = rinterp r env e*)
(*   prepass_sound, prepass_sound_real, prepass_sound_omega == the instances  *)
(*                    (generic posroot; b = true; om = true)                  *)
(*   radcan_eq_pre(_refined) (+ _odd, _neg, _real) == decision theorems:      *)
(*                    prepass on both sides, then the checker of the mode,    *)
(*                    conditions cs1 ++ cs2 ++ cs; real mode: b = true; neg   *)
(*                    mode: om = true needs smallroot w                       *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts RealRoot Syntax Mono Radcan.
From Radcan Require Import Refine Frac Denest OmegaRoot OmegaPass.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(* The pre-pass *)

Definition prepass_step (b om : bool) (e : rexpr) : rexpr * seq cond :=
  let: (e1, c1) := if om then omega_rw e else (e, [::]) in
  let: (e2, c2) := frac_split b e1 in
  let: (e3, c3) := denest_rwc e2 in
  (e3, c1 ++ c2 ++ c3).

Fixpoint prepass (b om : bool) (fuel : nat) (e : rexpr) : rexpr * seq cond :=
  match fuel with
  | O => (e, [::])
  | S n =>
    let: (e1, c1) := prepass_step b om e in
    if cmp_eqb (rexpr_cmp e1 e) then (e, [::])
    else let: (e2, c2) := prepass b om n e1 in (e2, c1 ++ c2)
  end.

(* Soundness *)

Section Sound.

Variables (F : numFieldType) (r : posroot F) (env : seq F).

Local Notation ri := (rinterp r env).

Definition omega_ok : Prop := forall e e' cs,
  omega_rw e = (e', cs) -> all_conds r env cs -> ri e' = ri e.

Lemma omega_ok_small (w : negroot r) : smallroot w -> omega_ok.
Proof. by move=> ov e e' cs; exact: (omega_rw_sound (env := env) ov). Qed.

Lemma prepass_step_sound (b om : bool) e e' cs :
  (b -> realroot r) -> (om -> omega_ok) ->
  prepass_step b om e = (e', cs) -> all_conds r env cs -> ri e' = ri e.
Proof.
move=> hb hom; rewrite /prepass_step.
case E1: (if om then omega_rw e else (e, [::])) => [e1 c1].
have S2 := @frac_split_sound_gen F r env b e1 hb.
case: (frac_split b e1) S2 => e2 c2 /= S2.
have S3 := @denest_rwc_sound F r env e2.
case: (denest_rwc e2) S3 => e3 c3 /= S3 [<- <-].
case/all_conds_cat => h1 /all_conds_cat[h2 /all_condsP/S3 ->].
rewrite -S2; last exact: all_conds_bridge.
by case: om E1 hom => [E1 /(_ isT) hom|[<- _] _] //; apply: hom E1 h1.
Qed.

Lemma prepass_sound_gen (b om : bool) fuel e e' cs :
  (b -> realroot r) -> (om -> omega_ok) ->
  prepass b om fuel e = (e', cs) -> all_conds r env cs -> ri e' = ri e.
Proof.
move=> hb hom; elim: fuel e e' cs => [|n IH] e e' cs /=; first by case=> ->.
have := @prepass_step_sound b om e; case: (prepass_step b om e) => e1 c1 S1.
case: ifP => _; first by case=> ->.
have := IH e1; case: (prepass b om n e1) => e2 c2 S2 [<- <-].
case/all_conds_cat => h1 h2.
by rewrite (S2 _ _ erefl h2) (S1 _ _ hb hom erefl h1).
Qed.

Theorem prepass_sound fuel e e' cs :
  prepass false false fuel e = (e', cs) -> all_conds r env cs -> ri e' = ri e.
Proof. exact: prepass_sound_gen. Qed.

Theorem prepass_sound_real (rl : realroot r) fuel e e' cs :
  prepass true false fuel e = (e', cs) -> all_conds r env cs -> ri e' = ri e.
Proof. exact: prepass_sound_gen. Qed.

Theorem prepass_sound_omega (w : negroot r) (ov : smallroot w) fuel e e' cs :
  prepass false true fuel e = (e', cs) -> all_conds r env cs -> ri e' = ri e.
Proof. by apply: prepass_sound_gen => // _; apply: omega_ok_small ov. Qed.

End Sound.

(* Decision theorems: prepass on both sides, then the checker *)

Section Decide.

Variables (F : numFieldType) (r : posroot F) (env : seq F).

Local Notation ri := (rinterp r env).

Lemma pre_eq_gen (b om : bool) (chk : rexpr -> rexpr -> option (seq cond))
    fuel e1 e2 f1 f2 cs1 cs2 cs :
  (b -> realroot r) -> (om -> omega_ok r env) ->
  (forall e1 e2 cs, chk e1 e2 = Some cs -> all_conds r env cs ->
     ri e1 = ri e2) ->
  prepass b om fuel e1 = (f1, cs1) -> prepass b om fuel e2 = (f2, cs2) ->
  chk f1 f2 = Some cs -> all_conds r env (cs1 ++ cs2 ++ cs) -> ri e1 = ri e2.
Proof.
move=> hb hom hchk E1 E2 H /all_conds_cat[h1 /all_conds_cat[h2 h]].
rewrite -(prepass_sound_gen hb hom E1 h1) -(prepass_sound_gen hb hom E2 h2).
exact: hchk H h.
Qed.

(* the neg mode without omega_rw *)
Lemma smallroot_false (w : negroot r) : false -> smallroot w.
Proof. by []. Qed.

Lemma refine_conds cs rcs :
  refine cs = rcs -> all_rconds F (proot r) env rcs -> all_conds r env cs.
Proof.
by move=> Hr Hc; apply: all_conds_bridge_back; apply: refine_sound; rewrite Hr.
Qed.

Theorem radcan_eq_pre fuel e1 e2 f1 f2 cs1 cs2 cs :
  prepass false false fuel e1 = (f1, cs1) ->
  prepass false false fuel e2 = (f2, cs2) ->
  radcan_check f1 f2 = Some cs -> all_conds r env (cs1 ++ cs2 ++ cs) ->
  ri e1 = ri e2.
Proof. by apply: pre_eq_gen => // e3 e4 cs3; apply: radcan_eq_cond. Qed.

Theorem radcan_eq_pre_refined fuel e1 e2 f1 f2 cs1 cs2 cs rcs :
  prepass false false fuel e1 = (f1, cs1) ->
  prepass false false fuel e2 = (f2, cs2) ->
  radcan_check f1 f2 = Some cs -> refine (cs1 ++ cs2 ++ cs) = rcs ->
  all_rconds F (proot r) env rcs -> ri e1 = ri e2.
Proof.
by move=> E1 E2 H Hr Hc; apply: radcan_eq_pre E1 E2 H (refine_conds Hr Hc).
Qed.

Theorem radcan_eq_pre_odd (o : oddroot r) fuel e1 e2 f1 f2 cs1 cs2 cs :
  prepass false false fuel e1 = (f1, cs1) ->
  prepass false false fuel e2 = (f2, cs2) ->
  radcan_check_odd f1 f2 = Some cs -> all_conds r env (cs1 ++ cs2 ++ cs) ->
  ri e1 = ri e2.
Proof.
by apply: pre_eq_gen => // e3 e4 cs3; apply: (radcan_eq_cond_odd o).
Qed.

Theorem radcan_eq_pre_refined_odd (o : oddroot r) fuel e1 e2 f1 f2 cs1 cs2
    cs rcs :
  prepass false false fuel e1 = (f1, cs1) ->
  prepass false false fuel e2 = (f2, cs2) ->
  radcan_check_odd f1 f2 = Some cs -> refine (cs1 ++ cs2 ++ cs) = rcs ->
  all_rconds F (proot r) env rcs -> ri e1 = ri e2.
Proof.
move=> E1 E2 H Hr Hc.
exact: (radcan_eq_pre_odd o) E1 E2 H (refine_conds Hr Hc).
Qed.

(* neg mode: omega_rw runs (om = true) only with a smallroot w *)
Theorem radcan_eq_pre_neg (w : negroot r) (om : bool) (ov : om -> smallroot w)
    fuel e1 e2 f1 f2 cs1 cs2 cs :
  prepass false om fuel e1 = (f1, cs1) ->
  prepass false om fuel e2 = (f2, cs2) ->
  radcan_check_neg f1 f2 = Some cs -> all_conds r env (cs1 ++ cs2 ++ cs) ->
  ri e1 = ri e2.
Proof.
apply: pre_eq_gen => // [/ov/omega_ok_small //|e3 e4 cs3].
exact: (radcan_eq_cond_neg w).
Qed.

Theorem radcan_eq_pre_refined_neg (w : negroot r) (om : bool)
    (ov : om -> smallroot w) fuel e1 e2 f1 f2 cs1 cs2 cs rcs :
  prepass false om fuel e1 = (f1, cs1) ->
  prepass false om fuel e2 = (f2, cs2) ->
  radcan_check_neg f1 f2 = Some cs -> refine (cs1 ++ cs2 ++ cs) = rcs ->
  all_rconds F (proot r) env rcs -> ri e1 = ri e2.
Proof.
move=> E1 E2 H Hr Hc.
exact: (radcan_eq_pre_neg ov) E1 E2 H (refine_conds Hr Hc).
Qed.

(* real mode: frac_split true, odd roots of fractions split freely *)
Theorem radcan_eq_pre_real (rl : realroot r) fuel e1 e2 f1 f2 cs1 cs2 cs :
  prepass true false fuel e1 = (f1, cs1) ->
  prepass true false fuel e2 = (f2, cs2) ->
  radcan_check_real f1 f2 = Some cs -> all_conds r env (cs1 ++ cs2 ++ cs) ->
  ri e1 = ri e2.
Proof.
by apply: pre_eq_gen => // e3 e4 cs3; apply: (radcan_eq_cond_real rl).
Qed.

Theorem radcan_eq_pre_refined_real (rl : realroot r) fuel e1 e2 f1 f2 cs1 cs2
    cs rcs :
  prepass true false fuel e1 = (f1, cs1) ->
  prepass true false fuel e2 = (f2, cs2) ->
  radcan_check_real f1 f2 = Some cs -> refine (cs1 ++ cs2 ++ cs) = rcs ->
  all_rconds F (proot r) env rcs -> ri e1 = ri e2.
Proof.
move=> E1 E2 H Hr Hc.
exact: (radcan_eq_pre_real rl) E1 E2 H (refine_conds Hr Hc).
Qed.

End Decide.
