(* Cyp File with errors: the command succeeds all the same.  The errors
   of errors_file.md are printed (❌); a node with an error and a
   conclusion leaves it as a goal of the Proof block, named after the
   node; a node with no conclusion leaves none, its subnodes are checked.
   Only a statement that cannot be read stops the command
   (statement_error.md: a hypothesis of the statement does not parse). *)
From Stdlib Require Import ZArith Lia.
From CypV Require Import Cyp.
Open Scope Z_scope.

Cyp File "errors_file.md".
Show.
all: lia.
CypQed.
Print Assumptions errors_file.

Fail Cyp File "statement_error.md".
