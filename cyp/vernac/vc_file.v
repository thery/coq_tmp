(* Cyp File with a Proof block: the conditions of vc_file.md that the
   default tactics do not discharge are its goals, named after them. *)
From Stdlib Require Import ZArith Lia.
From CypV Require Import Cyp.
Open Scope Z_scope.

Cyp File "vc_file.md".
Proof.
  [c1a]: apply Z.sqrt_nonneg.
  [c1b]: apply Z.sqrt_nonneg.
CypQed.
Print Assumptions sqrt_sq_md.
