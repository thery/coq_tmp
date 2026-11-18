(* The coarse gap tactic of cyp, cyp_gap: a last try on a condition that
   its justification, the rules and the default tactics leave open
   (elpi/gaps.elpi says when it is tried, and how a proof turns it off).

   A short text leaves gaps: a step whose claim follows from the steps
   before it, but not by one rule.  cyp_gap tries a few ways to bridge
   them, each under a time limit of one second, so that a condition it
   cannot close costs at most a few seconds.  The ways and their order
   come from measurement on the conditions that cyp leaves open in
   xtext's texts (xtext/gaps/). *)

From Stdlib Require Import Lia.

(* the closing tactic after a preparation: proof search with the
   hypotheses, or equational reasoning *)
Ltac gap_close := solve [ eauto | congruence ].

(* a case analysis on every boolean of the context *)
Ltac bool_cases :=
  repeat match goal with b : bool |- _ => destruct b end;
  simpl in *; gap_close.

(* an induction on one binder of the goal, the first that works: the
   closing step of a proof by induction whose cases are claims *)
Ltac induction_on_binder :=
  match goal with
  | |- forall _ : _, _ =>
      let x := fresh "x" in
      first [ solve [ intro x; induction x; simpl in *; intros; gap_close ]
            | intro x; induction_on_binder ]
  end.

(* a case analysis on one variable of the context (not a proof), the first
   that works: the closing step of a proof by cases *)
Ltac case_on_variable :=
  match goal with
  | x : ?T |- _ =>
      match type of T with Prop => fail | _ => idtac end;
      solve [ destruct x; simpl in *; intros; gap_close ]
  end.

(* each way must close the goal within one second *)
Ltac cyp_gap :=
  first [ timeout 1 (solve [ intros; eauto ])
        | timeout 1 (solve [ intros; bool_cases ])
        | timeout 1 induction_on_binder
        | timeout 1 (solve [ intros; case_on_variable ]) ].
