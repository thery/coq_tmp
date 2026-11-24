(* The candidate tactics of the coarse gap tactic, tried one by one on each
   condition that cyp leaves open, with no time limit: each candidate is a
   bounded search, or a decision procedure that ends, or lia, nia behind
   lia_guard (../../prooftext/Tactics.v); for each
   candidate it prints  T name, Rocq's time line, then OK or KO.
   Used by probe.sh (Cyp File ... Proof. all: (match goal with |- _ => gap_probe end).
   Abort.; the match runs gap_probe goal by goal). *)
From Stdlib Require Import Lia Lra Setoid Morphisms.
From CypV Require Import Cyp.
From Cdcl Require Import Itauto.

(* t must close the goal (auto, for one, succeeds without closing it) *)
Ltac probe t := first [ assert_succeeds (time (solve [t])); idtac "OK" | idtac "KO" ].

(* the candidates, all after intros *)
Ltac t_assumption := intros; assumption.
Ltac t_reflexivity := intros; reflexivity.
Ltac t_easy := intros; easy.
Ltac t_auto := intros; auto.
Ltac t_eauto := intros; eauto.
(* the bounded versions, as cyp and xtext run them: tauto is itauto auto
   (fuel from the size of the formula), firstorder is bounded_firstorder,
   auto and eauto have depth 5, lia and nia are behind lia_guard *)
Ltac t_tauto := intros; itauto auto.
Ltac t_firstorder := intros; bounded_firstorder.
Ltac t_congruence := intros; congruence.
Ltac t_lia := intros; guarded_lia.
Ltac t_nia := intros; guarded_nia.
Ltac t_lra := intros; lra.
Ltac t_subst_auto := intros; subst; auto.
Ltac t_simpl_auto := intros; simpl in *; auto.
Ltac t_simpl_congruence := intros; simpl in *; congruence.
Ltac t_simpl_lia := intros; simpl in *; guarded_lia.
(* typeclasses eauto with a depth: without one, the search for instances
   has no bound *)
Ltac t_typeclasses := intros; typeclasses eauto 5.
Ltac t_constructor := intros; econstructor; eauto.
Ltac t_unfold_defs := intros; repeat match goal with x := _ |- _ => subst x end; auto.
Ltac t_bool_cases := intros; repeat match goal with b : bool |- _ => destruct b end; simpl in *; auto; congruence.
(* t, at most n times (n a nat), as repeat (which may not end: rewriting
   with x = f x); t is passed as ltac:(idtac; ...), so that it is run
   at each step and not once, when the argument is read *)
Ltac repeat_upto n t :=
  lazymatch n with
  | S ?m => tryif once t then repeat_upto m t else idtac
  | O => idtac
  end.
Ltac rewrite_steps := constr:(5%nat).
Ltac t_rewrite_hyps := intros;
  let n := rewrite_steps in
  repeat_upto n ltac:(idtac; match goal with H : _ = _ |- _ => rewrite H end); auto.
Ltac t_f_equal := intros; f_equal; auto.
Ltac t_auto_arith := intros; auto with arith.
Ltac t_simpl_eauto := intros; simpl in *; eauto.
Ltac t_subst_simpl_congruence := intros; subst; simpl in *; congruence.
Ltac t_simpl_firstorder := intros; simpl in *; bounded_firstorder.
(* induction on the first binder of the goal that allows it, the cases
   closed by eauto (resp. firstorder) *)
Ltac induction_then closer :=
  match goal with
  | |- forall _ : _, _ =>
      let x := fresh "x" in
      first [ solve [ intro x; induction x; simpl in *; intros; closer ]
            | intro x; induction_then closer ]
  end.
Ltac close_eauto := eauto.
Ltac close_firstorder := bounded_firstorder.
Ltac close_congruence := congruence.
(* case analysis on a variable of the context, the cases closed by eauto *)
Ltac case_then closer :=
  match goal with
  | x : ?T |- _ =>
      match type of T with Prop => fail | _ => idtac end;
      solve [ destruct x; simpl in *; intros; closer ]
  end.
Ltac t_case_eauto := intros; case_then close_eauto.
Ltac t_induction_eauto := idtac; induction_then close_eauto.
Ltac t_induction_firstorder := idtac; induction_then close_firstorder.
Ltac t_induction_congruence := idtac; induction_then close_congruence.

(* each probe begins with the line COND: Ltac cannot read the name of a goal
   (?c2a), so table.sh pairs the k-th COND with the k-th condition that cyp
   lists (its lines 🔶), the goals being in the order of the text *)
Ltac gap_probe :=
  idtac "COND";
  match goal with |- ?g => idtac "GOAL" g end;
  idtac "T assumption"; probe t_assumption;
  idtac "T reflexivity"; probe t_reflexivity;
  idtac "T easy"; probe t_easy;
  idtac "T auto"; probe t_auto;
  idtac "T eauto"; probe t_eauto;
  idtac "T tauto"; probe t_tauto;
  idtac "T firstorder"; probe t_firstorder;
  idtac "T congruence"; probe t_congruence;
  idtac "T lia"; probe t_lia;
  idtac "T nia"; probe t_nia;
  idtac "T lra"; probe t_lra;
  idtac "T subst_auto"; probe t_subst_auto;
  idtac "T simpl_auto"; probe t_simpl_auto;
  idtac "T simpl_congruence"; probe t_simpl_congruence;
  idtac "T simpl_lia"; probe t_simpl_lia;
  idtac "T typeclasses"; probe t_typeclasses;
  idtac "T constructor"; probe t_constructor;
  idtac "T unfold_defs"; probe t_unfold_defs;
  idtac "T bool_cases"; probe t_bool_cases;
  idtac "T rewrite_hyps"; probe t_rewrite_hyps;
  idtac "T f_equal"; probe t_f_equal;
  idtac "T auto_arith"; probe t_auto_arith;
  idtac "T simpl_eauto"; probe t_simpl_eauto;
  idtac "T subst_simpl_congruence"; probe t_subst_simpl_congruence;
  idtac "T simpl_firstorder"; probe t_simpl_firstorder;
  idtac "T induction_eauto"; probe t_induction_eauto;
  idtac "T case_eauto"; probe t_case_eauto;
  idtac "T induction_firstorder"; probe t_induction_firstorder;
  idtac "T induction_congruence"; probe t_induction_congruence;
  idtac "END".

(* cyp's own gap tactic (cyp/vernac/Gaps.v, a bounded search) *)
From CypV Require Gaps.
Ltac gap_final :=
  idtac "COND";
  match goal with |- ?g => idtac "GOAL" g end;
  idtac "T cyp_gap";
  first [ assert_succeeds (time (solve [Gaps.cyp_gap])); idtac "OK" | idtac "KO" ];
  idtac "END".

(* bounded_firstorder and other bounded searches, on every condition of a
   text (#[bare] Cyp File): PROBE=fo_probe.  The measurement of
   firstorder itself (gaps/README.md) needed a time limit, and is not
   rerun; tauto and intuition are run as itauto *)
Ltac r_firstorder := intros; bounded_firstorder.
Ltac r_auto := intros; auto.
Ltac r_tauto := intros; itauto auto.
Ltac r_eauto2 := intros; eauto 2.
Ltac r_eauto3 := intros; eauto 3.
Ltac r_eauto4 := intros; eauto 4.
Ltac r_eauto5 := intros; eauto 5.
Ltac r_intuition_eauto2 := intros; itauto (eauto 2).
Ltac r_intuition_eauto3 := intros; itauto (eauto 3).
Ltac fo_probe :=
  idtac "COND";
  idtac "T bounded_firstorder"; probe r_firstorder;
  idtac "T auto"; probe r_auto;
  idtac "T tauto"; probe r_tauto;
  idtac "T eauto2"; probe r_eauto2;
  idtac "T eauto3"; probe r_eauto3;
  idtac "T eauto4"; probe r_eauto4;
  idtac "T eauto5"; probe r_eauto5;
  idtac "T itauto_eauto2"; probe r_intuition_eauto2;
  idtac "T itauto_eauto3"; probe r_intuition_eauto3;
  idtac "END".

(* a bounded first-order search: decompose_all (../../prooftext/Tactics.v,
   at most decompose_steps steps), then a proof search of bounded depth *)
Ltac r_bfo_auto := decompose_all; auto.
Ltac r_bfo_eauto2 := decompose_all; eauto 2.
Ltac r_bfo_eauto3 := decompose_all; eauto 3.
Ltac r_bfo_eauto4 := decompose_all; eauto 4.
Ltac r_ri_eauto3 := repeat intro; eauto 3.
Ltac fo2_probe :=
  idtac "COND";
  idtac "T bfo_auto"; probe r_bfo_auto;
  idtac "T bfo_eauto2"; probe r_bfo_eauto2;
  idtac "T bfo_eauto3"; probe r_bfo_eauto3;
  idtac "T bfo_eauto4"; probe r_bfo_eauto4;
  idtac "T ri_eauto3"; probe r_ri_eauto3;
  idtac "END".

