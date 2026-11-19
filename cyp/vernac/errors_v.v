(* Nodes with errors: the command succeeds all the same.  Each error is
   printed (❌), and a node with an error and a conclusion leaves its
   conclusion as a goal of the Proof block, named after the node, that the
   nodes after it still use.  A node with no conclusion is used by
   nothing; its subnodes are checked all the same. *)
From Stdlib Require Import ZArith Lia PrimString List.
From CypV Require Import Cyp.
Import ListNotations.
Open Scope Z_scope.
Open Scope pstring_scope.

(* 1: a justification that names nothing; 2: false, left as a goal; 3: no
   tagged formula, a remark.  The goals: ?c1 (the error of 1) and ?c2. *)
Cyp Lemma errs (a b : Z) (H : 0 < a < b) : a * a < b * b :=
  [ "By *nothing_here*{.just} we have" (0 < a) "{.claim}" ;
    "Hence" (0 < a - b) "{.claim}" ;
    "Note that" (0 < b) "and so on" ].
Show.
[c1]: lia.
Fail CypQed.
Abort.

(* One error of each kind, and the lemma proved in the Proof block:
   1 a fact that is no hypothesis: its conclusion 0 < a is the goal ?c1;
   2 proved from 1 (c1 in its context);
   3 two conclusions: a node with no conclusion, used by nothing; its
     subnode 3.1 is checked all the same;
   4 a conclusion that does not type-check: no conclusion;
   5 a hypothesis that does not type-check, left out of the node: 5 is
     proved without it;
   6 a justification out of scope (k is the hypothesis of 5): the goal ?c6;
   0 the statement, from 2 and 6. *)
Cyp Lemma errs_all (a b : Z) (H : 0 < a < b) : a * a < b * b :=
  [ "From" (a = 1) "{.fact} we have" (0 < a) "{.claim}" ;
    "Hence" (0 < b) "{.claim}" ;
    "We have" (0 < a + b) "{.claim} and" (0 < b - a) "{.claim}"
      [ "Indeed" (0 <= a) "{.claim}" ] ;
    "Also" (0 < a + true) "{.claim}" ;
    "Assume" (a = true) "{.hyp} (k). Then" (0 < b * b) "{.claim}" ;
    "By *k*{.just} we have" (0 < b - a) "{.claim}" ].
Show.
[c1]: lia.
[c6]: lia.
CypQed.
Check errs_all.
