# Cyp Lemma: a cyp proof as a Rocq command (prototype)

A proof written as text, checked step by step, entirely inside Rocq: the
statement is an ordinary lemma statement, the body a list of steps mixing
words (strings) and formulas (Rocq terms, parsed by Rocq).

```coq
From Stdlib Require Import ZArith Lia PrimString List.
Require Import Cyp.
Import ListNotations.
Open Scope Z_scope.
Open Scope pstring_scope.

Cyp Lemma square_pos (a b : Z) (H : 0 < a < b) : a * a < b * b :=
  [ "It is equivalent to prove" (0 < b * b - a * a) ;
    "That can also be written as" (0 < (b + a) * (b - a)) ;
    "From" (0 < a < b) "we have" (0 < b + a) "and" (0 < b - a) ].
```

prints

```
cyp: square_pos
  ✅ It is equivalent to prove `0 < b * b - a * a`
  ✅ That can also be written as `0 < (b + a) * (b - a)`
  ✅ From `0 < a < b` we have `0 < b + a` and `0 < b - a`
  ✅ the statement follows
cyp: square_pos proved
```

and defines `square_pos` as a theorem (`Print Assumptions`: closed under
the global context).  If a step is not proved, the command fails, says
which steps, and defines nothing ([wrong.v](wrong.v)).

How it works ([Cyp.v](Cyp.v), Rocq-Elpi): the command receives the body
unchecked (raw arguments) with the lemma's variables bound.  The words
before a formula give its role, as in the Markdown cyp; a formula that is
not a proposition is a mention.  Each step is proved when it is read, in
its own context (the lemma's variables and hypotheses and the claims of the
steps before it), by the rules of the database `cyp.db` (`justify`
clauses, as in the Markdown cyp) or by the default tactics; its proof term
goes into the proof of the lemma: a forward step is `let c : C := P in ...`,
a backward step a proof of `C -> Goal` applied to the proof of `C`.

Build: `rocq c -R . CypV Cyp.v`, then the examples.

Not yet: local scopes (Let/Assume), French and Italian words, a printer
writing the Markdown version.
