# cyp inside Rocq: Cyp File and Cyp Lemma

The library [Cyp.v](Cyp.v) (Rocq-Elpi, opam switch `elpi4`) is cyp
itself: what a proof means, how its steps are checked, and how the
Markdown is read and written back.  It gives two commands.

Build: `rocq c -Q . CypV Cyp.v`.

## Cyp File: a proof in Markdown

```coq
From Stdlib Require Import ZArith Lia.
From CypV Require Import Cyp.
Open Scope Z_scope.
Elpi CypFile "square_pos.md".
```

reads the proof, parses each formula between backticks in the context of
its step (`coq.parse.argument`, in the scope of the header's `scope:`),
checks every step, writes `square_pos.checked.md` and `square_pos.cyp.json`
next to it, and defines the lemma when every step is proved.  The program
`cyp` ([../bin/cyp.ml](../bin/cyp.ml)) writes this small file from the
proof's header (its `require:`, `rules:` and `flags:`) and runs it; the
Markdown format is described in [../README.md](../README.md).

Tests here: [since_demo.md](since_demo.md) (a claim used by the next claim
of the same step), [scope_demo.md](scope_demo.md) (nested local scopes),
[square_pos_fr.md](square_pos_fr.md) and [square_pos_it.md](square_pos_it.md)
(French and Italian).

## Cyp Lemma: the same proof as a Rocq command

The statement is an ordinary lemma statement, the body a list of steps
mixing words (strings) and formulas (Rocq terms, parsed by Rocq):

```coq
From Stdlib Require Import ZArith Lia PrimString List.
From CypV Require Import Cyp.
Import ListNotations.
Open Scope Z_scope.
Open Scope pstring_scope.

Cyp Lemma square_pos (a b : Z) (H : 0 < a < b) : a * a < b * b :=
  [ "It is equivalent to prove" (0 < b * b - a * a) ;
    "That can also be written as" (0 < (b + a) * (b - a)) ;
    "From" (0 < a < b) "we have" (0 < b + a) "and" (0 < b - a) ].
```

prints one ✅ or ❌ per step and defines `square_pos` when every step is
proved ([square_pos.v](square_pos.v)); a word `"by X"` in a step is its
justification ([named_v.v](named_v.v)).  If a step is not proved, the
command fails, says which, and defines nothing ([wrong.v](wrong.v)).
[lemma1.v](lemma1.v) is Lemma 1 of the exp paper written this way, with
the same rules as [../exp/lemma1.md](../exp/lemma1.md).

## How it works

The Elpi files of [elpi/](elpi):

- `text.elpi`: words, formulas, tags `{.role}`, names `(h)`, the
  justification `*by X*`, and the role of a formula from the last phrase
  before it;
- `vocab_en.elpi`, `vocab_fr.elpi`, `vocab_it.elpi`: the phrases of each
  language and the role they give;
- `check.elpi`: closing a goal by the step's justification, the rules of
  the database `cyp.db`, or the default tactics;
- `proof.elpi`: the proof of a statement from its steps; a forward claim is
  `let c : C := P in ...`, a backward step a proof of `C -> Goal` applied
  to a proof of `C`, a local scope a proof of its claims generalised over
  its variables and hypotheses;
- `markdown.elpi`: reading the Markdown, writing the checked Markdown and
  the JSON for the editor.

The default tactics (`lia`, `lra`, ...) are called through a table of Ltac
definitions in [Cyp.v](Cyp.v): Rocq-Elpi cannot yet run a tactic given by
its name or its code as a string.

The proof term is built by cyp and type-checked by Rocq before the lemma is
defined: `Print Assumptions` shows only the axioms of the libraries used.
