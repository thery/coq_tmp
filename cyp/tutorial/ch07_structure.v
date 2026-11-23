(* cyp tutorial, example 07: structure (cyp/TUTORIAL.md, section 4).

   In ch07_structure.md, step 1 assumes P (p).  The hypothesis p holds in
   step 1 and in its sub-steps, nowhere else.  Its conclusion, R /\ Q, is
   in the closing paragraph, after the sub-steps.  Seen from step 2, step
   1 is the formula P -> R /\ Q.

   #[bare] CypFile prints the conditions, the goals cyp would try, one
   per step, and tries none of them. *)
From CypV Require Import Cyp.

#[bare] CypFile "cyp-tutorial/ch07_structure.md".
CypFile "cyp-tutorial/ch07_structure.md".
Check structure.
