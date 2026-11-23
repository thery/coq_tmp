(* cyp tutorial, example 03: claims and facts (cyp/TUTORIAL.md, section 3).

   A claim is what a step proves.  A fact is a formula the step uses: it
   must already be known, a hypothesis or the claim of a step that the
   step can see.  cyp checks that it is known; it does not prove it.

   In ch03_facts.md, step 3 claims something false: it is not proved
   (❌).  Step 4 uses it as a fact: the fact is known (it is the claim of
   step 3), so step 4 is proved (✅), as on paper.  Step 5 uses a fact
   that nothing gives: an error.  The lemma is not defined, so CypFile
   fails. *)
From Stdlib Require Import Arith Lia.
From CypV Require Import Cyp.

Fail CypFile "cyp-tutorial/ch03_facts.md".

(* Cyp File (two words) takes a Proof block: what cyp did not prove is
   left there as goals, named after the steps: ?c3 and ?c5. *)
Cyp File "cyp-tutorial/ch03_facts.md".
Proof.
  Show.
Abort.
