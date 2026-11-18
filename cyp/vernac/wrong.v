(* A false step: its condition 1 is left to the Proof block, where it
   cannot be proved, so the lemma is not defined. *)
From Stdlib Require Import ZArith Lia PrimString List.
From CypV Require Import Cyp.
Import ListNotations.
Open Scope Z_scope.
Open Scope pstring_scope.

Cyp Lemma wrong (a b : Z) (H : 0 < a < b) : a * a < b * b :=
  [ "From" (0 < a < b) "we have" (0 < a - b) ;
    "Hence" (0 < b + a) ].
Proof.
  Fail lia.
Abort.
Fail Check wrong.
