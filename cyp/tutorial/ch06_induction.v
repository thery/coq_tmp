(* cyp tutorial, example 06: induction (cyp/TUTORIAL.md, section 3).

   *induction*{.just} on *l*{.just} is an induction on the list l.  The
   two sub-steps are the two cases: the empty list, and x :: l' with the
   induction hypothesis IH. *)
From Stdlib Require Import List Lia. Import ListNotations.
From CypV Require Import Cyp.

CypFile "cyp-tutorial/ch06_induction.md".
Check length_app.
