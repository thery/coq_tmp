From elpi Require Import elpi.

(* here is a short summary of how Elpi modes work.

As you know, in Elpi you have input and output modes.

Below I ignore output mode since, normally, it creates no problem in understanding its behavior.

In a predicate p with the signature
p i:term
with the two rules:
r1 := p {{nat /\ X}}.
r2 := p {{bool /\ X}} :- X = {{unit}}.

*)

Elpi Program mode lp:{{

pred p i:term.

p {{nat /\ lp:X}}.
p {{bool /\ lp:X}} :- X = {{unit}}.

}}.

(*
In this program, all calls to p are such that the first argument acts as a 
pattern: its variables are not instantiated when unifying it with the head of 
the clause

In an input argument we perform matching instead of unification.
That is, if h1 is an input argument in the head of a clause and c1 is the 
corresponding argument in the query, then pattern_match h1 c1 works as follows:
the variables in c1 are frozen (they cannot be instantiated), while variables 
in h1 can be unified. After matching, c1 and h1 must be equal under the new 
substitution.

*)

(*
Examples
*)

(*
The query p {{nat /\ Z}} uses rule r1.
We have pattern_match {{nat /\ X}} {{nat /\ Z}}.
It succeeds by making Z equal to X (X is not “touched”); concretely, 
Z points to X (or Z → X).
*)

Elpi Query lp:{{
  p {{nat /\ lp:Z}}.
}}.

(*
The query p {{nat /\ nat}} also uses rule r1.
We have pattern_match {{nat /\ X}} {{nat /\ nat}}.
This matching succeeds by putting X = {{nat}}.
*)

Elpi Query lp:{{
  p {{nat /\ nat}}.
}}.

(*
The query p {{Z /\ nat}} uses rule r1.
We have pattern_match {{nat /\ X}} {{Z /\ nat}}.
This matching fails: the only way to make {{nat /\ X}} and {{Z /\ nat}} equal 
is to set X = {{nat}} and Z = {{nat}}, but since we are matching, Z cannot be 
instantiated.
*)

Fail Elpi Query lp:{{
  p {{lp:Z /\ nat}}.
}}.

(* 
--------------------------------
*)

(* 
To answer Laurent’s (and maybe Yves’s) remark: when we enter the body of a rule, 
the variables that were in input position lose their “non-instantiable” status.

For instance, the call p {{bool /\ Z}} W will use rule r2.
We have pattern_match {{bool /\ X}} {{bool /\ Z}}.
Matching succeeds by making X point to Z (or X → Z).
Then we enter the body of the rule and encounter X = {{unit}} (the first premise 
of r2).
This unification sets X to unit; since X was pointing to Z, Z also becomes unit.
(Technically, this uses dereferencing behind the scenes.)
*)

Elpi Query lp:{{
  p {{bool /\ lp:X}}.
}}.

(*
Conclusion

Question: If a variable is in input position, am I not allowed to instantiate 
it?
Answer: It depends on where the unification happens.

   You do not instantiate an input variable when matching it in the head of a 
   rule.

   You lose the non-instantiability of an input variable in the body of the 
   rule; in the body the variable can be assigned.

Therefore: there is no "mode checking" on variables in Elpi.
The pattern_match predicate

In the latest Elpi release, we have a new pattern_match predicate, which behaves 
exactly as Thomas needs in his PBP.

As Laurent told me, you have a term and a pattern, and you want to instantiate
 only the pattern (if I recall correctly).

The predicate pattern_match does what you expect:

    pattern_match [X, Y] [1, 2]. succeeds: it instantiates X and Y to 1 and 2.

    pattern_match [1, 2] [X, Y] fails, since the variables on the right-hand 
    side cannot be instantiated.
*)

Elpi Query lp:{{
  pattern_match [X, Y] [1, 2].
}}.

Fail Query lp:{{
  pattern_match [1, 2] [X, Y].
}}.


(* 
Digression

In standard Prolog there are no modes (and no signatures), so the two rules below are equivalent:

r3 := p 3.
r4 := p X :- X = 3.

In Elpi, modes play an important role.

If the signature of p is pred p o:int, then r3 and r4 are equivalent.
If the signature of p is pred p i:int, then r3 and r4 are not equivalent.

*)

Elpi Accumulate lp:{{

pred p_i i:term.

p_i {{3}} :- coq.say "first rule".
p_i X :-  X = {{3}}, coq.say "second rule".

}}.

Elpi Query lp:{{
  p_i {{3}}.
}}.

Elpi Query lp:{{
  p_i X.
}}.


(*
In the second scenario:

    the query p Z will fail in r3 (in matching we cannot assign Z to 3 in 
    the head of the clause)

    the query p Z will succeed in r4: matching makes X point to Z, 
    then we unify X with 3, and Z becomes 3 as a side effect.
*)

(*
A further remark

Why are Elpi input variables not “forever” non-instantiable?
i.e. why, in the body of rule r4, are we allowed to change the value of input variables?

This is because we are doing meta-programming.
Small concrete example

From elpi Require Import elpi.
*)

Elpi Tactic solve_nat.
Elpi Accumulate  lp:{{

  pred my_solve i:term, o:term.
  my_solve {{lp:X = lp:Y}} {{eq_refl}} :- X = Y.

  solve (goal _ _ Ty _ _ as G) Sol :-
    my_solve Ty S,
    refine S G Sol.
}}.

Goal exists N, N = 3.
Proof.
  eexists.
  elpi solve_nat.
  Show Proof.
Qed.

(*
In the example, the tactic my_solve expects an input term: we want to match the
first argument to see if we have an eq as head.

Then we want to ensure that X and Y are unifiable, and more than that we 
really want to make the two terms equal.

In the Proof, we really want that the variable N, which is mapped to the 
elpi variable X, is assigned to 3.

-- 
*)

