From Stdlib Require Import Reals Lra PrimString List.
From CypV Require Import Cyp.
Import ListNotations.
Open Scope R_scope.
(* the rules named monotonicity, then the word declared: *monotonicity*{.just}
   means these rules, and only them *)
Elpi Accumulate cyp.db lp:{{
  named "monotonicity" {{ (_ * _ <= _ * _)%R }} (apply {{ Rmult_le_compat_r }}).
  named "monotonicity" {{ (_ * _ <= _ * _)%R }} (apply {{ Rmult_le_compat_l }}).
}}.
CypJustification "monotonicity" := rules.
(* a word for an Ltac tactic of the proof *)
Ltac easy_check := lra.
CypJustification "checked" := easy_check.
Open Scope pstring_scope.
Cyp Lemma named_v (a b c d : R) (Ha : 0 <= a <= b) (Hc : 0 <= c <= d) : a * c <= b * d :=
  [ "we have" (a * c <= b * c) "{.claim} by *monotonicity*{.just}" ;
    "and" (b * c <= b * d) "{.claim} by *monotonicity*{.just}" ].
Proof. CypQed.
Cyp Lemma checked_v (a b : R) (Ha : a <= b) : a + 1 <= b + 1 :=
  [ "we have" (a + 1 <= b + 1) "{.claim}, as *checked*{.just}" ].
Proof. CypQed.
(* the reason given does not prove the step: its condition is left *)
Cyp Lemma named_bad (a : R) (Ha : 0 <= a) : 0 <= a :=
  [ "we have" (0 <= a) "{.claim} by *monotonicity*{.just}" ].
Proof.
Fail CypQed.
Abort.
(* a word declared twice, a word for no tactic, rules that do not exist *)
Fail CypJustification "checked" := lra.
Fail CypJustification "nothing" := no_such_tactic.
Fail CypJustification "none" := rules.
(* a word not declared: the node's error says how to declare it *)
Cyp Lemma undeclared (a : R) (Ha : 0 <= a) : 0 <= a :=
  [ "we have" (0 <= a) "{.claim} by *positivity*{.just}" ].
Proof.
  [c1]: exact Ha.
CypQed.
