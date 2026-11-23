(* cyp tutorial, example 01: a first proof (cyp/TUTORIAL.md, section 2).

   The proof is the text ch01_first.md (open it in the Files panel).
   A formula between backquotes is used by cyp only when it has a class:
   `n : nat`{.var} a variable, `0 < n`{.hyp} (h) a hypothesis named h,
   `n < 2 * n`{.claim} the conclusion of a step, `0 < n`{.fact} a fact
   the step uses.  Each list item is a step.

   CypFile reads the text, turns each step into a Rocq goal, tries to
   prove it, and writes ch01_first.checked.md: the same text with ✅ in
   front of each proved step.  When every step is proved, the lemma
   double_gt is defined.

   The Require line is the text's "require:" header: CypFile does not run
   it, so the file does. *)
From Stdlib Require Import Arith Lia.
From CypV Require Import Cyp.

CypFile "cyp-tutorial/ch01_first.md".
Check double_gt.
