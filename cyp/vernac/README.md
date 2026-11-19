# cyp inside Rocq: Cyp File and Cyp Lemma

The library [Cyp.v](Cyp.v) (Rocq-Elpi, opam switch `elpi5`) is cyp
itself: what a proof means, how its nodes are checked, and how the
Markdown is read and written back.  It gives two commands.

Build: `rocq c -Q . CypV Cyp.v`.

## Cyp File: a proof in Markdown

```coq
From Stdlib Require Import ZArith Lia.
From CypV Require Import Cyp.
Open Scope Z_scope.
CypFile "square_pos.md".
```

reads the proof into its tree of nodes (prooftext's reader), parses
each formula between backticks in the context of its node (`coq.parse.argument`, in the scope of the header's `scope:`),
checks every node, writes `square_pos.checked.md` and `square_pos.cyp.json`
next to it, and defines the lemma when every node is proved.  The program
`cyp` ([../bin/cyp.ml](../bin/cyp.ml)) writes this small file from the
proof's header (its `require:`, `rules:` and `flags:`) and runs it; the
Markdown format is described in [../README.md](../README.md).

Tests here: [since_demo.md](since_demo.md) (a span inside a list item: a
conclusion used by the conclusion around it), [scope_demo.md](scope_demo.md)
(nested scopes, a closing paragraph), [type_demo.md](type_demo.md)
(variables of type `Type`, in the statement and in a scope),
[claims_demo.md](claims_demo.md) (nodes with subnodes, named nodes,
nested scopes with several variables, a closing paragraph, several
justifications), [nest_demo.md](nest_demo.md) (13 nested nodes), and
[square_pos_fr.md](square_pos_fr.md), ... in ten languages (the words
may be in any language: cyp reads only the tags).

## The text as a verification condition generator

Each node gives one condition, its conclusion in its own context, numbered
like the node in Dewey notation: `2.1` is the first subnode of node 2,
`0` the top node, the statement.  In a goal, the nodes before it are
plain hypotheses (`c1`, `c2_1`, or the name the text gives a conclusion,
`(n)`), each as ∀ V, H → C, whatever their proof.  cyp discharges each
condition by the justifications and facts of its node, its rules and its
default tactics; with a Proof block, the conditions it does not
discharge are the goals of the block, in the order of the text, each
named after its number: `c`, then the number with its dots written `_`
(a Rocq name cannot begin with a digit nor hold a dot), the same name as
the node's hypothesis in the goals after it (when the text gives it no
name).  Condition `1` is the goal `?c1`, condition `2.1` the goal
`?c2_1`, condition `0` the goal `?c0`.
The script proves a condition by its name, in any order, with Rocq's goal
selectors:

```coq
Cyp File "vc_file.md".
Proof.
  [c2]: apply Z.sqrt_nonneg.
  [c1]: apply Z.sqrt_nonneg.
CypQed.
```

(`[c1]: { tac. }` for several tactics.)  The goal of condition 2 reads

```
1 goal (?c2)

  a, b : Z
  H1 : 0 <= a
  H2 : 0 <= b
  c1 : 0 <= Z.sqrt a
  ============================
  0 <= Z.sqrt b
```

and the checked Markdown marks the nodes 🔶 **[1]** and 🔶 **[2]**
([vc_file.md](vc_file.md), [vc_file.v](vc_file.v); the same with Cyp
Lemma: [vc_demo.v](vc_demo.v); the node 3, `[c3]:`, in
[bare_demo.v](bare_demo.v)).  The proof is closed by `CypQed.`, not
`Qed.` (Rocq-Elpi does not let `Qed` close a proof opened by an Elpi
command).  The names are given by `coq.ltac.name-uvar` of rocq-elpi
master (switch `elpi5`).  Ltac cannot read the name of a goal: a tactic
run on every goal (`all: tac.`) does not know which condition it is on.

`CypFile "proof.md".`, used by the program `cyp`, has no Proof block:
a condition it does not discharge is ❌ and the lemma is not defined.

**Always succeeds, leaves goals.**  `Cyp File` and `Cyp Lemma` succeed
whatever their nodes say: what is proved is proved, and the rest is left
as goals of the Proof block.  An error of a node (a justification that
names nothing, a fact not in scope, a name out of scope, an unknown
class, an unclosed span, two conclusions, a formula that does not
parse...) is printed, `❌ 1 sqrt_magic names nothing known...`, marked ❌
in the checked Markdown and the JSON, and the command goes on:

- a node with an error and a conclusion C: its condition is not tried
  (the error is the reason), C is the goal of the Proof block named
  after the node (`?c1`), and the nodes after it use C as usual;
- a node with no conclusion (none, two, or one that does not parse or is
  no proposition): there is no goal; the node is used by nothing, its
  subnodes are checked all the same and each is used by the subnodes
  after it (not outside the node: the scope rules are unchanged);
- a variable, a hypothesis or a definition that does not parse: reported,
  and left out of its node (the node is proved without it).

The commands fail only when the statement cannot be read whole: in `Cyp
File`, the conclusion or a variable or hypothesis of the statement does
not parse ([statement_error.md](statement_error.md)); in `Cyp Lemma`, the
statement does not type-check (Rocq's message) or is no proposition; and
on errors of Rocq outside cyp (a library not found, a proof term that
Rocq rejects).  [errors_v.v](errors_v.v) (Cyp Lemma, an example of each
error, `Show.` listing the goals ?c1 and ?c6) and
[errors_file.v](errors_file.v) (Cyp File on [errors_file.md](errors_file.md))
are the tests.  `CypFile` (no Proof block) and the program `cyp` treat a
node with an error as a node not proved: the checked Markdown and the
JSON are written, and the lemma is not defined.

**Bare mode.**  With `#[bare]` (`#[bare] Cyp File "p.md".`, `#[bare] Cyp
Lemma ...`), nothing is tried: every condition is a goal of the Proof
block ([bare_demo.v](bare_demo.v)).  `#[bare] CypFile "p.md".` only
prints the conditions with their contexts; the program `cyp` does it with
`cyp --conditions p.md`.

**The gap tactic.**  A condition that the rules and the default tactics
leave open is tried with `cyp_gap` ([Gaps.v](Gaps.v)) before it is left
to the Proof block; `#[gaps="off"]` (`#[gaps="off"] Cyp Lemma ...`, or
the header line `gaps: off` of a Markdown proof) turns it off.

**Timing.**  With the environment variable `CYP_TIME` set, cyp prints the
time spent on each condition (`cyp: time 2.1 1234 ms`).

**Justifications.**  A justification that names no rule, hypothesis, node,
variable, lemma or tactic (for instance tactic code) is an error of its
node (../README.md, "The format").

## Cyp Lemma: the same proof as a Rocq command

The statement is an ordinary lemma statement, the body the list of the
subnodes of the top node.  Each is a node written in Rocq, as a list item
of a Markdown text: words (strings, read as the text of a node, so that
`*X*{.just}` is a justification), formulas (Rocq terms, parsed by Rocq),
each followed by a string that starts with its class, `"{.claim}"`, and a
list of steps among its arguments, its subnodes.  An untagged term is
plain text, as in Markdown.  The binders of the statement are the
variables and hypotheses of the top node, its type its conclusion; the
same tree as a Markdown text is then checked, with no lines (the
messages give none):

```coq
From Stdlib Require Import ZArith Lia PrimString List.
From CypV Require Import Cyp.
Import ListNotations.
Open Scope Z_scope.
Open Scope pstring_scope.

Cyp Lemma square_pos (a b : Z) (H : 0 < a < b) : a * a < b * b :=
  [ "It is equivalent to prove" (0 < b * b - a * a) "{.claim}."
      [ "That can also be written as" (0 < (b + a) * (b - a)) "{.claim}."
          [ "From" (0 < a < b) "{.fact} we have" (0 < b + a /\ 0 < b - a) "{.claim}." ] ] ].
Proof. CypQed.
```

defines `square_pos`
([square_pos.v](square_pos.v)); `"{.claim} by *monotonicity*{.just}"` gives
a formula its class and the node a justification ([named_v.v](named_v.v)).  A false node leaves a condition
that the Proof block cannot prove ([wrong.v](wrong.v)).
(A lemma of the private case study has also been written this way.)

## How it works

The Elpi files of [elpi/](elpi), with prooftext's reader
([../../prooftext](../../prooftext/README.md): `tree.elpi`, the tree of
nodes of a text, `nodes.elpi`, what each node says and the errors of the
tree, `formulas.elpi`, the parts of a text, `tactics.elpi`, the tactics a
text may name):

- `text.elpi`: what cyp takes from the text of a node, its tagged parts
  only (a formula's role is its class; no word gives a role);
- `check.elpi`: closing a goal by the justifications and the facts of its
  node (the rule and tactic names choose the method, the other names are
  handed to it, put first by `cyp_first`), the rules of the database
  `cyp.db`, or the default tactics;
- `gaps.elpi`: the gap tactic, a last try on a condition left open
  (`cyp_gap` of [Gaps.v](Gaps.v), a bounded search), and its switch;
- `command.elpi`: what the commands share (reading a file, checking its
  tree, counting, defining the lemma);
- `proof.elpi`: the condition of each node and the proof of the
  statement: a node is `fun V H => cyp_have T1 C P1 (fun c1 : T1 => ...)`,
  each subnode given once to `cyp_have` as ∀ V, H → C, so that the proof
  term grows linearly with the nesting ([nest_demo.md](nest_demo.md): 13
  nested nodes, type-check 35 ms and definition 27 ms); the facts looked
  up among the hypotheses in scope, up to conversion;
- `markdown.elpi`: the checked Markdown (the lines of the text, with the
  marks and messages of the nodes inserted) and the JSON for the editor.

The default tactics (`lia`, `lra`, ...) are called through a table of Ltac
definitions in [Cyp.v](Cyp.v): Rocq-Elpi cannot yet run a tactic given by
its name or its code as a string.

The proof term is built by cyp and type-checked by Rocq before the lemma is
defined: `Print Assumptions` shows only the axioms of the libraries used.
