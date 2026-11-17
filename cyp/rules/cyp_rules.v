(* The rule database of cyp and the tactic that uses it.  A rule file of a
   proof adds clauses [justify Pattern Tac] to cyp.db:
     justify Pattern (ltac "name")  on a goal that matches Pattern, try the
                                    Ltac1 tactic [name]; it must close the
                                    goal;
     justify Pattern (lemma T)      refine the goal with T, then close each
                                    premise with the rules again.
   The rules are tried in order; the first one that closes the goal wins. *)
From elpi Require Import elpi.

Elpi Db cyp.db lp:{{
  kind cyptac type.
  type ltac string -> cyptac.
  type lemma term -> cyptac.
  pred justify i:term, o:cyptac.
}}.

Elpi Tactic cyp_by.
Elpi Accumulate Db cyp.db.
Elpi Accumulate lp:{{
  pred run i:cyptac, i:goal, o:list sealed-goal.
  run (ltac N) G GL :- coq.ltac.call-ltac1 N G GL.
  run (lemma T) G GL :-
    refine T G GL1, coq.ltac.all (coq.ltac.open solve) GL1 GL.

  solve (goal _ _ Ty _ _ as G) [] :- justify Ty Tac, run Tac G [].
}}.
