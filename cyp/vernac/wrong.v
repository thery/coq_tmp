From Stdlib Require Import ZArith Lia PrimString List.
From CypV Require Import Cyp.
Import ListNotations.
Open Scope Z_scope.
Open Scope pstring_scope.

Fail Cyp Lemma wrong (a b : Z) (H : 0 < a < b) : a * a < b * b :=
  [ "From" (0 < a < b) "we have" (0 < a - b) ;
    "Hence" (0 < b + a) ].
Fail Check wrong.
