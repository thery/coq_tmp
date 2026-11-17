(* The rule database of cyp and the tactic that uses it.  A rule file of a
   proof adds clauses [justify Pattern Tac] to cyp.db:
     justify Pattern (ltac "name")  on a goal that matches Pattern, try the
                                    Ltac1 tactic [name]; it must close the
                                    goal;
     justify Pattern (lemma T)      refine the goal with T, then close each
                                    premise with the rules again;
     justify Pattern (apply T)      apply the lemma T, its arguments found
                                    by unification, then the same.
   The rules are tried in order; the first one that closes the goal wins.
   Conjunctions and disjunctions are handled by cyp itself. *)
From elpi Require Import elpi.

Elpi Db cyp.db lp:{{
  kind cyptac type.
  type ltac string -> cyptac.
  type lemma term -> cyptac.
  % [apply T]: apply the lemma T (its arguments are found by unification),
  % then close each premise with the rules again
  type apply term -> cyptac.
  pred justify i:term, o:cyptac.
  % [justify_first Pattern Tac]: the same, tried before every [justify]
  % rule, for the rules of one proof that must win over shared ones
  pred justify_first i:term, o:cyptac.
}}.

Ltac cyp_eapply t := eapply t.
(* the default tactics of a proof (its header's by:), redefined for it *)
Ltac cyp_default := fail.
Ltac cyp_split := split.
Ltac cyp_left := left.
Ltac cyp_right := right.

Elpi Tactic cyp_by.
Elpi Accumulate Db cyp.db.
Elpi Accumulate lp:{{
  % [close G]: some rule closes the goal G; premises of a lemma are closed
  % by [close] again, so that a failure backtracks to the next rule
  pred close i:goal.
  % a conjunction: both sides; a disjunction: one side, then the other.
  % The two sides are taken from the goal, so that the new holes live
  % under the goal's variables.
  close (goal _ _ {{ _ /\ _ }} _ _ as G) :-
    coq.ltac.call-ltac1 "cyp_split" G GL, premises GL.
  close (goal _ _ {{ _ \/ _ }} _ _ as G) :-
    coq.ltac.call-ltac1 "cyp_left" G GL, premises GL.
  close (goal _ _ {{ _ \/ _ }} _ _ as G) :-
    coq.ltac.call-ltac1 "cyp_right" G GL, premises GL.
  close (goal _ _ Ty _ _ as G) :- justify_first Ty Tac, run Tac G.
  close (goal _ _ Ty _ _ as G) :- justify Ty Tac, run Tac G.

  pred premises i:list sealed-goal.
  premises GL :- coq.ltac.all (coq.ltac.open close-tac) GL [].

  pred run i:cyptac, i:goal.
  run (ltac N) G :- coq.ltac.call-ltac1 N G [].
  run (lemma T) G :- refine T G GL, premises GL.
  run (apply T) G :- coq.ltac.call "cyp_eapply" [trm T] G GL, premises GL.

  % a premise: the rules, else the default tactics of the proof
  pred close-tac i:goal, o:list sealed-goal.
  close-tac G [] :- close G, !.
  close-tac G [] :- coq.ltac.call-ltac1 "cyp_default" G [].

  solve G [] :- close G, !.
  % no rule closes the goal: an ordinary tactic failure, only here at the
  % top, so that the default tactics are tried next
  solve _ _ :- coq.ltac.fail 0 "cyp: no rule closes this goal".
}}.
