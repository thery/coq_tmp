(* cyp tutorial, example 04: justifications (cyp/TUTORIAL.md, section 3).

   *X*{.just} names what a step uses: a hypothesis, *hp*{.just}; an
   earlier step, *c1*{.just} for step 1, or the name the text gives it,
   *pn*{.just}; a lemma, *Nat.add_0_r*{.just}; or a tactic word,
   *lia*{.just}.  A step may have several. *)
From Stdlib Require Import Arith Lia.
From CypV Require Import Cyp.

CypFile "cyp-tutorial/ch04_justifications.md".
Check justifications.
