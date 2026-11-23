(* cyp tutorial, example 12: the Proof block (cyp/TUTORIAL-2.md, section 8).

   In ch12_goals.md, the default tactic lia knows nothing of Z.sqrt:
   step 1 is not proved.  Step 2 is an open goal, `0 <= Z.sqrt b`{.goal}:
   the author leaves it to prove, and cyp does not try it.  Step 3 uses
   both.

   With Cyp File, the two are the goals ?c1 and ?c2 of the Proof block,
   proved by their names, in any order; CypQed ends the proof. *)
From Stdlib Require Import ZArith Lia.
From CypV Require Import Cyp.
Open Scope Z_scope.

Cyp File "cyp-tutorial/ch12_goals.md".
Proof.
  Show.
  [c2]: apply Z.sqrt_nonneg.
  [c1]: apply Z.sqrt_nonneg.
CypQed.
Check goals.
