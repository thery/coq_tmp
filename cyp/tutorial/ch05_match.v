(* cyp tutorial, example 05: case analysis (cyp/TUTORIAL.md, section 3).

   *match*{.just} on *h*{.just} takes the hypothesis h apart (Rocq's
   destruct); *ex*{.just} says its type.  The sub-steps are the cases:
   here one case, with a witness k and the equation hk. *)
From Stdlib Require Import Arith Lia.
From CypV Require Import Cyp.

CypFile "cyp-tutorial/ch05_match.md".
Check even_plus_two.
