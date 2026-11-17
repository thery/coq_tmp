(* The rules of rules_demo.md: a product of nonnegative numbers is
   monotone; everything linear is left to lra. *)
Ltac real_lra := lra.
Elpi Accumulate cyp.db lp:{{
  justify {{ (_ * _ <= _ * _)%R }} (lemma {{ Rmult_le_compat _ _ _ _ _ _ _ _ }}).
  justify {{ (_ * _ <= _ * _)%R }} (lemma {{ Rmult_le_compat_r _ _ _ _ _ }}).
  justify {{ (_ * _ <= _ * _)%R }} (lemma {{ Rmult_le_compat_l _ _ _ _ _ }}).
  justify {{ (_ <= _)%R }} (ltac "real_lra").
}}.
