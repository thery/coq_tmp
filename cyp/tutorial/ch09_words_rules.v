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
