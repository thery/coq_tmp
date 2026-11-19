(* Bare mode: every condition is a goal of the Proof block, in the order
   of the text, named after it (?c3 for 3); nothing is tried. *)
From Stdlib Require Import ZArith Lia.
From CypV Require Import Cyp.
Open Scope Z_scope.

#[bare] Cyp File "vc_file.md".
Proof.
  [c3]: nia.
  all: first [ apply Z.sqrt_nonneg | assumption | nia ].
CypQed.
Print Assumptions sqrt_sq_md.

(* the conditions only, as cyp --conditions shows them *)
#[bare] CypFile "vc_file.md".
