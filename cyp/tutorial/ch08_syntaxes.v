(* cyp tutorial, example 08: two syntaxes (cyp/TUTORIAL.md, section 5).

   ch08_structured.md writes a proof with lists: an item is a step.
   ch08_free.md writes the same proof as prose: a span [ ... ]{.p} is a
   step, and a div ::: p ... ::: is a step of several paragraphs.  cyp
   reads the same tree from both. *)
From CypV Require Import Cyp.

CypFile "cyp-tutorial/ch08_structured.md".
CypFile "cyp-tutorial/ch08_free.md".
Check praeclarum.
Check praeclarum_free.
