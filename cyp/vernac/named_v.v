From Stdlib Require Import Reals Lra PrimString List.
Require Import Cyp.
Import ListNotations.
Open Scope R_scope.
Elpi Accumulate cyp.db lp:{{
  named "monotonicity" {{ (_ * _ <= _ * _)%R }} (apply {{ Rmult_le_compat_r }}).
  named "monotonicity" {{ (_ * _ <= _ * _)%R }} (apply {{ Rmult_le_compat_l }}).
}}.
Open Scope pstring_scope.
Cyp Lemma named_v (a b c d : R) (Ha : 0 <= a <= b) (Hc : 0 <= c <= d) : a * c <= b * d :=
  [ "we have" (a * c <= b * c) "by monotonicity" ;
    "and" (b * c <= b * d) "by monotonicity" ].
Fail Cyp Lemma named_bad (a : R) (Ha : 0 <= a) : 0 <= a :=
  [ "we have" (0 <= a) "by monotonicity" ].
