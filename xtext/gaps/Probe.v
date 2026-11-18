(* The candidate tactics of the coarse gap tactic, tried one by one on each
   condition that cyp leaves open, each under a time limit; for each
   candidate it prints  T name, Rocq's time line, then OK or KO.
   Used by probe.sh (Cyp File ... Proof. all: (match goal with |- _ => gap_probe end).
   Abort.; the match runs gap_probe goal by goal). *)
From Stdlib Require Import Lia Lra Setoid Morphisms.
From CypV Require Import Cyp.

(* t must close the goal (auto, for one, succeeds without closing it) *)
Ltac probe t := first [ assert_succeeds (timeout 2 (time (solve [t]))); idtac "OK" | idtac "KO" ].

(* the candidates, all after intros *)
Ltac t_assumption := intros; assumption.
Ltac t_reflexivity := intros; reflexivity.
Ltac t_easy := intros; easy.
Ltac t_auto := intros; auto.
Ltac t_eauto := intros; eauto.
Ltac t_tauto := intros; tauto.
Ltac t_firstorder := intros; firstorder.
Ltac t_congruence := intros; congruence.
Ltac t_lia := intros; lia.
Ltac t_nia := intros; nia.
Ltac t_lra := intros; lra.
Ltac t_subst_auto := intros; subst; auto.
Ltac t_simpl_auto := intros; simpl in *; auto.
Ltac t_simpl_congruence := intros; simpl in *; congruence.
Ltac t_simpl_lia := intros; simpl in *; lia.
Ltac t_typeclasses := intros; typeclasses eauto.
Ltac t_constructor := intros; econstructor; eauto.
Ltac t_unfold_defs := intros; repeat match goal with x := _ |- _ => subst x end; auto.
Ltac t_bool_cases := intros; repeat match goal with b : bool |- _ => destruct b end; simpl in *; auto; congruence.
Ltac t_rewrite_hyps := intros; repeat match goal with H : _ = _ |- _ => rewrite H end; auto.
Ltac t_f_equal := intros; f_equal; auto.
Ltac t_auto_arith := intros; auto with arith.
Ltac t_simpl_eauto := intros; simpl in *; eauto.
Ltac t_solve_proper := intros; solve_proper.
Ltac t_subst_simpl_congruence := intros; subst; simpl in *; congruence.
Ltac t_simpl_firstorder := intros; simpl in *; firstorder.
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
Ltac close_firstorder := firstorder.
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

Ltac gap_probe :=
  match goal with c := cyp_condition ?n |- _ => idtac "COND" n end;
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
  idtac "T solve_proper"; probe t_solve_proper;
  idtac "T subst_simpl_congruence"; probe t_subst_simpl_congruence;
  idtac "T simpl_firstorder"; probe t_simpl_firstorder;
  idtac "T induction_eauto"; probe t_induction_eauto;
  idtac "T case_eauto"; probe t_case_eauto;
  idtac "T induction_firstorder"; probe t_induction_firstorder;
  idtac "T induction_congruence"; probe t_induction_congruence;
  idtac "END".
