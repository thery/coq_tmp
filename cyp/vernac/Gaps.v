(* The coarse gap tactic of cyp, cyp_gap; it uses the bounded first-order
   search shared with xtext (prooftext/Tactics.v).

   cyp_gap is a last try on a condition that its justification, the rules
   and the default tactics leave open (elpi/gaps.elpi says when it is
   tried, and how a proof turns it off).  A short text leaves gaps: a step
   whose claim follows from the steps before it, but not by one rule.
   cyp_gap tries a few ways to bridge them.  Each way is a bounded search
   (a proof search of bounded depth, case analyses on the variables there
   are), with no time limit: it fails after a bounded number of steps.  The
   ways and their order come from measurement on the conditions that cyp
   leaves open in xtext's texts (xtext/gaps/README.md). *)

From ProofText Require Export Tactics.

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

(* the ways, the most useful first *)
Ltac cyp_gap :=
  first [ bounded_firstorder
        | solve [ intros; bool_cases ]
        | induction_on_binder
        | solve [ intros; case_on_variable ]
        (* a constructor whose arguments the search finds (a witness) *)
        | solve [ intros; econstructor; gap_close ] ].
