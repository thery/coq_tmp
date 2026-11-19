(* Cyp Lemma: the steps of square_pos as nodes written in Rocq.  A string
   right after a formula gives its class, "{.claim}"; a list among the
   arguments of a step is the list of its subnodes. *)
From Stdlib Require Import ZArith Lia PrimString List.
From CypV Require Import Cyp.
Import ListNotations.
Open Scope Z_scope.
Open Scope pstring_scope.

Cyp Lemma square_pos (a b : Z) (H : 0 < a < b) : a * a < b * b :=
  [ "It is equivalent to prove" (0 < b * b - a * a) "{.claim}."
      [ "That can also be written as" (0 < (b + a) * (b - a)) "{.claim}."
          [ "From" (0 < a < b) "{.fact} we have" (0 < b + a /\ 0 < b - a) "{.claim}." ] ] ].
Proof. CypQed.

Check square_pos.
Print Assumptions square_pos.
