(* cyp tutorial, example 11: when something is wrong (cyp/TUTORIAL-2.md,
   section 7).

   ch11_errors.md has one mistake per step: a false claim, a name that
   names nothing, a fact not known, a step with no conclusion, a name out
   of its scope, a step with two conclusions, an unknown class, a formula
   that does not parse.  cyp reports each at its step and goes on.

   CypFile fails (the lemma is not defined).  Cyp File always succeeds:
   each step with a conclusion that cyp did not prove is a goal of the
   Proof block. *)
From Stdlib Require Import Arith Lia.
From CypV Require Import Cyp.

Fail CypFile "cyp-tutorial/ch11_errors.md".

Cyp File "cyp-tutorial/ch11_errors.md".
Proof.
  Show.
Abort.
