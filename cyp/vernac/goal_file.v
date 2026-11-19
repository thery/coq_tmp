(* A proof in progress, as ExtractText_partial writes it: its open goals,
   `B`{.goal} and `A`{.goal}, are not tried; they are the goals ?c1_1_1
   and ?c1_1_2 of the Proof block, and the nodes after them use them (the
   closing paragraph of 1.1, then node 1, are proved with them).  Node 1
   is a case analysis justified by the type *and*{.just} and the method
   *match*{.just}. *)
From CypV Require Import Cyp.

Cyp File "goal_file.md".
Proof.
  Show.
  [c1_1_1]: assumption.
  [c1_1_2]: assumption.
CypQed.
Print Assumptions goal_demo.
