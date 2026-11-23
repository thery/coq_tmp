(* The rules of named_demo.md: a product of nonnegative reals is monotone
   in each factor, the rules named monotonicity *)
Elpi Accumulate cyp.db lp:{{
  named "monotonicity" {{ (_ * _ <= _ * _)%R }} (apply {{ Rmult_le_compat_r }}).
  named "monotonicity" {{ (_ * _ <= _ * _)%R }} (apply {{ Rmult_le_compat_l }}).
}}.
(* the justification *monotonicity*{.just} means these rules, and only them *)
CypJustification "monotonicity" := rules.
