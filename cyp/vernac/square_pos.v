From Stdlib Require Import ZArith Lia PrimString List.
From CypV Require Import Cyp.
Import ListNotations.
Open Scope Z_scope.
Open Scope pstring_scope.

Cyp Lemma square_pos (a b : Z) (H : 0 < a < b) : a * a < b * b :=
  [ "It is equivalent to prove" (0 < b * b - a * a) ;
    "That can also be written as" (0 < (b + a) * (b - a)) ;
    "From" (0 < a < b) "we have" (0 < b + a) "and" (0 < b - a) ].
Proof. CypQed.

Check square_pos.
Print Assumptions square_pos.
