(* cyp tutorial, example 02: the roles (cyp/TUTORIAL.md, section 3).

   ch02_roles.md shows each role once:
   - `a b : nat`{.var} two variables, `s := a + b`{.var} a local definition;
   - `a <= b`{.hyp} (hab) a named hypothesis, `b <= 10`{.hyp} an unnamed
     one: cyp calls it H1;
   - `a <= 10`{.claim} (ha) the conclusion of a step, with a name;
   - `a <= 10`{.fact} a fact: a formula already known;
   - *hab*{.just} a justification: a name the step uses;
   - a line with no tag: a remark, shown (▫️) and not checked. *)
From Stdlib Require Import Arith Lia.
From CypV Require Import Cyp.

CypFile "cyp-tutorial/ch02_roles.md".
Check roles.
