(******************************************************************************)
(* Dispatch: one checker and one soundness theorem for every mode.            *)
(* The facts known about the root structure r select the checker.  They are   *)
(* collected by typeclass resolution, so the tactic never names them.         *)
(*   rfact P       == option P: the fact P, if known (class; found as a       *)
(*                    hypothesis or as a global instance, None otherwise)     *)
(*   wfacts w      == the facts on w : negroot r (record of rfact: cycroot,   *)
(*                    cycprim, smallroot, gaussroot)                          *)
(*   negfacts r    == option {w : negroot r & wfacts w}: a negroot of r (a    *)
(*                    hypothesis or an instance) with its facts               *)
(*   rfacts r      == the facts on r: realroot r, oddroot r, negfacts r       *)
(*   shape         == which facts are present (booleans, computable)          *)
(*   shape_of fs   == the shape of fs : rfacts r                              *)
(*   radcan_check_w s == the checker of the negroot modes (merged omegas,     *)
(*                    cyclotomic reduction, then any sqrt n as a sum of     *)
(*                    omegas by Gauss sums, GaussMode.v)                      *)
(*   radcan_check_shape pre s == the checker of the shape: realroot first,    *)
(*                    then oddroot, then the negroot modes (only the plain    *)
(*                    neg mode after the pre-pass, pre = true), then the      *)
(*                    generic radcan_check                                    *)
(*   radcan_eq_cond_shape, radcan_eq_refined_shape == the decision theorems,  *)
(*                    raw (all_conds) and refined (Refine.v) conditions       *)
(*   radcan_eq_pre_shape, radcan_eq_pre_refined_shape == the same after the   *)
(*                    pre-pass of Prepass.v (frac_split true in real mode,    *)
(*                    omega_rw in neg mode with a smallroot)                  *)
(*   facts_tt r, facts_odd o, facts_real rl, facts_neg w, facts_cyc cy,       *)
(*   facts_cycprim cy cp == rfacts r with exactly the given facts (resolved   *)
(*                    in an empty context)                                    *)
(*   instances on C (n.-root): rootC_negroot C with cycroot, cycprim,         *)
(*                    smallroot, gaussroot; on R (rootR): rootR_realroot R    *)
(* Adding a fact P on w : negroot r with its checker radcan_check_new (and    *)
(* its theorem radcan_eq_cond_new w (h : P w) : radcan_check_new e1 e2 =      *)
(* Some cs -> all_conds r env cs -> rinterp r env e1 = rinterp r env e2):     *)
(*   1. a field wf_new : rfact (P w) in wfacts                                *)
(*   2. a field sh_new : bool in shape, and its line in shape_of              *)
(*      (wbit (fun w h => isSome (wf_new h)) (rf_neg fs))                     *)
(*   3. a branch in radcan_check_w (the stronger checkers first)              *)
(*   4. the case of the branch in radcan_eq_cond_w (case: on the new field    *)
(*      of the record, then exact: (radcan_eq_cond_new h H Hc))               *)
(*   5. optionally an instance #[global] Instance : rfact (P (rootC_negroot   *)
(*      C)) := Some .. for n.-root goals (all hints are global: active as     *)
(*      soon as Dispatch is required, Tactic.v users need not import it)      *)
(* Tactic.v is unchanged: the fact is found as a hypothesis h : P w of the    *)
(* context by typeclass resolution.                                           *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot RootC RootR Syntax Radcan Refine RealRoot.
From Radcan Require Import OmegaRoot OmegaC OmegaRoot2 OddRoot NegRootC.
From Radcan Require Import AbsRoot NegCyc CycC Prepass Cyclo CycloC.
From Radcan Require Import GaussMode GaussC.
From Radcan Require Import CycloInv. (* CycloInv *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(* Facts, collected by typeclass resolution *)

Class rfact (P : Prop) := rfact_opt : option P.

#[global] Instance rfact_none (P : Prop) : rfact P | 100 := None.
#[global] Hint Extern 1 (rfact ?P) =>
  match goal with h : P |- _ => exact (Some h) end : typeclass_instances.

Section Facts.

Variables (F : numFieldType) (r : posroot F).

Record wfacts (w : negroot r) : Type := WFacts {
  wf_cyc : rfact (cycroot w);
  wf_prim : rfact (cycprim w);
  wf_small : rfact (smallroot w);
  wf_gauss : rfact (gaussroot w)
}.

Definition negfacts : Type := option {w : negroot r & wfacts w}.

Record rfacts : Type := RFacts {
  rf_real : rfact (realroot r);
  rf_odd : rfact (oddroot r);
  rf_neg : negfacts
}.

End Facts.

Existing Class wfacts.
Existing Class negfacts.
Existing Class rfacts.

#[global] Hint Extern 0 (wfacts _) => constructor : typeclass_instances.
#[global] Hint Extern 0 (rfacts _) => constructor : typeclass_instances.
#[global] Instance negfacts_none (F : numFieldType) (r : posroot F) :
  negfacts r | 100 := None.
#[global] Hint Extern 1 (negfacts ?r) =>
  match goal with
  | w : negroot r |- _ => exact (Some (@existT _ (@wfacts _ r) w _))
  end
  : typeclass_instances.

(* the instances on C and R *)

#[global] Instance rootC_cyc_fact (C : numClosedFieldType) :
  rfact (cycroot (rootC_negroot C)) := Some (rootC_cycroot C).
#[global] Instance rootC_prim_fact (C : numClosedFieldType) :
  rfact (cycprim (rootC_negroot C)) := Some (rootC_cycprim C).
#[global] Instance rootC_small_fact (C : numClosedFieldType) :
  rfact (smallroot (rootC_negroot C)) := Some (rootC_smallroot C).
#[global] Instance rootC_gauss_fact (C : numClosedFieldType) :
  rfact (gaussroot (rootC_negroot C)) := Some (rootC_gaussroot C).
#[global] Instance rootC_negfacts (C : numClosedFieldType) :
  negfacts (rootC_posroot C) :=
  Some (@existT _ (@wfacts _ (rootC_posroot C)) (rootC_negroot C) _).
#[global] Instance rootR_real_fact (R : rcfType) :
  rfact (realroot (rootR_posroot R)) := Some (rootR_realroot R).

(* rfacts r with exactly the given facts *)

Section Explicit.

Variables (F : numFieldType) (r : posroot F).

Definition facts_tt : rfacts r := _.
Definition facts_odd (o : oddroot r) : rfacts r := _.
Definition facts_real (rl : realroot r) : rfacts r := _.
Definition facts_neg (w : negroot r) : rfacts r := _.
Definition facts_cyc (w : negroot r) (cy : cycroot w) : rfacts r := _.
Definition facts_cycprim (w : negroot r) (cy : cycroot w) (cp : cycprim w) :
  rfacts r := _.

End Explicit.

(* Shapes *)

Record shape := Shape {
  sh_real : bool; sh_odd : bool; sh_neg : bool;
  sh_cyc : bool; sh_prim : bool; sh_small : bool; sh_gauss : bool
}.

(* a boolean on the facts of the negroot, false without one *)
Definition wbit (F : numFieldType) (r : posroot F)
    (f : forall w : negroot r, wfacts w -> bool) (n : negfacts r) : bool :=
  if n is Some (existT w h) then f w h else false.

Definition shape_of (F : numFieldType) (r : posroot F) (fs : rfacts r) :=
  Shape (isSome (rf_real fs)) (isSome (rf_odd fs)) (isSome (rf_neg fs))
    (wbit (fun w h => isSome (wf_cyc h)) (rf_neg fs))
    (wbit (fun w h => isSome (wf_prim h)) (rf_neg fs))
    (wbit (fun w h => isSome (wf_small h)) (rf_neg fs))
    (wbit (fun w h => isSome (wf_gauss h)) (rf_neg fs)).

(* The checkers *)

(* the Gauss-sum mode (GaussMode.v), only when the cyclotomic checker fails *)
Definition gauss_or (s : shape) (o : option (seq cond)) (e1 e2 : rexpr) :
    option (seq cond) :=
  if o is Some cs then Some cs
  else if sh_gauss s then radcan_check_gauss e1 e2 else None.

Definition radcan_check_w (s : shape) (e1 e2 : rexpr) : option (seq cond) :=
  if sh_cyc s then
    if sh_prim s then
      gauss_or s (radcan_check_cyc2 e1 e2) e1 e2 (* CycloInv, Gauss *)
    else radcan_check_negc e1 e2
  else radcan_check_neg e1 e2.

Definition radcan_check_shape (pre : bool) (s : shape) (e1 e2 : rexpr) :
    option (seq cond) :=
  if sh_real s then radcan_check_real e1 e2
  else if sh_odd s then radcan_check_odd e1 e2
  else if sh_neg s then
    if pre then radcan_check_neg e1 e2 else radcan_check_w s e1 e2
  else radcan_check e1 e2.

(* the pre-pass flags of the shape: frac_split true in real mode, omega_rw *)
(* in neg mode with a smallroot                                            *)
Definition pre_real (s : shape) := sh_real s.
Definition pre_omega (s : shape) :=
  ~~ sh_real s && ~~ sh_odd s && sh_neg s && sh_small s.

(* the pre-pass of the shape *)
Definition prepass_shape (s : shape) := prepass (pre_real s) (pre_omega s).

Section Decide.

Variables (F : numFieldType) (r : posroot F) (env : seq F).

Local Notation ri := (rinterp r env).

Lemma radcan_eq_cond_w (w : negroot r) (h : wfacts w) e1 e2 cs :
  radcan_check_w (shape_of (RFacts None None (Some (existT _ w h)))) e1 e2
    = Some cs ->
  all_conds r env cs -> ri e1 = ri e2.
Proof.
case: h => hc hp hm hg; rewrite /radcan_check_w => H Hc.
case: hc H => [cy|] H; last exact: (radcan_eq_cond_neg w H Hc).
case: hp H => [cp|] H; last exact: (radcan_eq_cond_negc cy H Hc).
(* CycloInv, then Gauss *)
case/ocase_some: H => H; first exact: (radcan_eq_cond_cyc2 cy cp H Hc).
case: hg H => // gs H; exact: (radcan_eq_cond_gauss cy cp gs H Hc).
Qed.

Theorem radcan_eq_cond_shape (pre : bool) (fs : rfacts r) e1 e2 cs :
  radcan_check_shape pre (shape_of fs) e1 e2 = Some cs ->
  all_conds r env cs -> ri e1 = ri e2.
Proof.
case: fs => hr ho hn; rewrite /radcan_check_shape => H Hc.
case: hr H => [rl|] H; first exact: (radcan_eq_cond_real rl H Hc).
case: ho H => [o|] H; first exact: (radcan_eq_cond_odd o H Hc).
case: hn H => [[w h]|] H; last exact: (radcan_eq_cond H Hc).
case: pre H => H; first exact: (radcan_eq_cond_neg w H Hc).
exact: (radcan_eq_cond_w H Hc).
Qed.

Theorem radcan_eq_refined_shape (pre : bool) (fs : rfacts r) e1 e2 cs rcs :
  radcan_check_shape pre (shape_of fs) e1 e2 = Some cs -> refine cs = rcs ->
  all_rconds F (proot r) env rcs -> ri e1 = ri e2.
Proof.
by move=> H Hr Hc; apply: radcan_eq_cond_shape H (refine_conds Hr Hc).
Qed.

Lemma pre_omega_ok (fs : rfacts r) :
  pre_omega (shape_of fs) -> omega_ok r env.
Proof.
case: fs => hr ho [[w [hc hp [hv|] hg]]|] Hs.
  exact: omega_ok_small hv.
all: by move: Hs; rewrite /pre_omega /= !(andbF, andFb).
Qed.

Lemma pre_real_ok (fs : rfacts r) : pre_real (shape_of fs) -> realroot r.
Proof. by case: fs => [[rl|]]. Qed.

Theorem radcan_eq_pre_shape (fs : rfacts r) fuel e1 e2 f1 f2 cs1 cs2 cs :
  prepass_shape (shape_of fs) fuel e1 = (f1, cs1) ->
  prepass_shape (shape_of fs) fuel e2 = (f2, cs2) ->
  radcan_check_shape true (shape_of fs) f1 f2 = Some cs ->
  all_conds r env (cs1 ++ cs2 ++ cs) -> ri e1 = ri e2.
Proof.
apply: pre_eq_gen; [exact: pre_real_ok | exact: pre_omega_ok |].
exact: radcan_eq_cond_shape.
Qed.

Theorem radcan_eq_pre_refined_shape (fs : rfacts r) fuel e1 e2 f1 f2 cs1 cs2
    cs rcs :
  prepass_shape (shape_of fs) fuel e1 = (f1, cs1) ->
  prepass_shape (shape_of fs) fuel e2 = (f2, cs2) ->
  radcan_check_shape true (shape_of fs) f1 f2 = Some cs ->
  refine (cs1 ++ cs2 ++ cs) = rcs ->
  all_rconds F (proot r) env rcs -> ri e1 = ri e2.
Proof.
move=> E1 E2 H Hr Hc.
exact: radcan_eq_pre_shape E1 E2 H (refine_conds Hr Hc).
Qed.

End Decide.
