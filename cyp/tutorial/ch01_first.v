(* cyp tutorial, example 01: a first proof (cyp/TUTORIAL.md, section 2).

   The text is ch01_first.md.  It gives no justification: it only says
   what each step claims.  Each step gives one condition, a Rocq goal:
   its claim, below the variables and hypotheses in scope and the claims
   of the steps before it.

   1. With #[bare], cyp tries nothing: every condition is a goal of the
      Proof block, named after its step (?c1, ?c2, ?c3, and ?c0 for the
      statement).  Show cN shows one; they are ordinary Rocq goals, proved
      here by hand.  (Each run is in its own module, as each defines the
      lemma sqrt_le.) *)
From Stdlib Require Import Arith Lia.
From CypV Require Import Cyp.

Module Conditions.
#[bare] Cyp File "cyp-tutorial/ch01_first.md".
Proof.
  Show c1.
  Show c2.
  Show c3.
  Show c0.
  [c1]: apply Nat.sqrt_le_lin.
  [c2]: lia.
  [c3]: split; [lia | exact c2].
  [c0]: exact c3.
CypQed.
End Conditions.

(* 2. Without #[bare], cyp tries its default tactics (here lia, from the
      header's "by:" line, then its own) on the same conditions.  It
      closes 2, 3 and 0; lia knows nothing of Nat.sqrt, so ?c1 is left
      to the Proof block. *)
Module Tried.
Cyp File "cyp-tutorial/ch01_first.md".
Proof.
  Show.
  [c1]: apply Nat.sqrt_le_lin.
CypQed.
End Tried.

(* 3. A justification tells cyp how to prove a condition: in
      ch01_first_just.md, step 1 names the lemma *Nat.sqrt_le_lin*{.just}.
      The condition is the same; cyp now proves it, and the lemma is
      defined with no Proof block (CypFile, one word, as the program cyp
      runs it). *)
CypFile "cyp-tutorial/ch01_first_just.md".
Check sqrt_le_just.
