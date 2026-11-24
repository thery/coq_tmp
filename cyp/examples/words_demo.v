(* The words of words_demo.md: a justification word may be several words,
   as a paper writes them: *monotone product*{.just} *)
Elpi Accumulate cyp.db lp:{{
  named "monotone product" {{ (_ * _ <= _ * _)%R }} (apply {{ Rmult_le_compat_r }}).
  named "monotone product" {{ (_ * _ <= _ * _)%R }} (apply {{ Rmult_le_compat_l }}).
}}.
(* the rules named "monotone product", and only them *)
CypJustification "monotone product" := rules.
(* an Ltac tactic; the blanks are collapsed: the word is "linear arithmetic" *)
Ltac words_lra := lra.
CypJustification "linear  arithmetic" := words_lra.
