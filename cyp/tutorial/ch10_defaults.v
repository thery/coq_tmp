(* cyp tutorial, example 10: no justification (cyp/TUTORIAL.md, section 6).

   A step with no justification is tried with the rules, then the tactics
   of the header's "by:" line, then cyp's own (tauto, lia, nia, lra), and
   last with the gap tactic, a short bounded search.  Here step 2 needs a
   case analysis on o: only the gap tactic finds it.  ch10_no_gaps.md is
   the same text with the header line "gaps: off": step 2 is not proved. *)
From Stdlib Require Import Arith Lia.
From CypV Require Import Cyp.

CypFile "cyp-tutorial/ch10_defaults.md".
Fail CypFile "cyp-tutorial/ch10_no_gaps.md".
