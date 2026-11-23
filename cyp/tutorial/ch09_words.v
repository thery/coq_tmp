(* cyp tutorial, example 09: declaring justification words
   (cyp/TUTORIAL.md, section 6).

   What a word means is written in the proof's files.  The lines between
   the two "rules" marks below are the file ch09_words_rules.v, which the
   header of ch09_words.md names ("rules: ch09_words_rules.v") for the
   program cyp; here they are run before CypFile.

   - *arithmetic*{.just} runs the Ltac tactic arith_check;
   - *monotonicity*{.just} means the Elpi rules named "monotonicity",
     and only them: step 4, a sum, fits no rule and is not proved. *)

(* rules: begin *)
(* The words of ch09_words.md, read by the program cyp from its header:
   "rules: ch09_words_rules.v". *)
From Stdlib Require Import Arith Lia.
From CypV Require Import Cyp.

Ltac arith_check := lia.
CypJustification "arithmetic" := arith_check.

Elpi Accumulate cyp.db lp:{{
  named "monotonicity" {{ (_ * _ <= _ * _)%nat }} (apply {{ Nat.mul_le_mono_r }}).
  named "monotonicity" {{ (_ * _ <= _ * _)%nat }} (apply {{ Nat.mul_le_mono_l }}).
}}.
CypJustification "monotonicity" := rules.
(* rules: end *)

Fail CypFile "cyp-tutorial/ch09_words.md".
