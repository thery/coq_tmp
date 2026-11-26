#set document(title: "Selecting subterms: a tutorial")
#set page(paper: "a4", margin: 2.2cm, numbering: "1")
#set text(size: 10.5pt)
#set heading(numbering: "1.")
#show raw: set text(size: 9.5pt)
#let tgt(x) = underline(stroke: 1.2pt + red, offset: 2pt, x)
#let yes = text(fill: green.darken(30%))[univocal]
#let no(n) = text(fill: red.darken(20%))[#n positions]

#align(center)[
  #text(size: 16pt, weight: "bold")[Selecting subterms] \
  #text(size: 11pt)[A tutorial of the selector library] \
  #v(0.3em)
  #text(size: 9pt)[Draft. After G. Gonthier and E. Tassi, _A language of patterns for
  subterm selection_, ITP 2012.]
]

= What a selector is

Many proof commands act on part of the goal: `rewrite`, `set`, `elim`, the
generalization `:` of ssreflect, and the actions of proof by pointing. A
*selector* says which part. It *denotes* a set of positions of the goal. It is
*univocal* when that set has exactly one element.

The set can be larger than one because of how ssreflect reads a pattern: it
designates _all the occurrences of the first instance_. "First instance" means
the first subterm, in pre-order (left to right, outside in), that matches the
pattern. "Its occurrences" means all the subterms equal to that instance.

= The kinds of selectors

#table(
  columns: (auto, auto, 1fr),
  inset: 5pt,
  stroke: 0.4pt + luma(180),
  table.header([*kind*], [*form*], [*what it says*]),
  table.cell(colspan: 3)[*A. Absolute*: no description of the subterm],
  [A1 path], [`"2.3.1"`], [the route from the root: one position],
  [A2 occurrence], [`{k}t`], [the k-th occurrence of a fully given term `t`],
  [A3 range], [characters], [a span of the printed goal],
  table.cell(colspan: 3)[*B. Redex patterns*: describe the subterm itself],
  [B1 closed term], [`[a - b]`], [the term, with no hole],
  [B2 term with holes], [`[_ - b]`], [a term with holes; the search is keyed by its head],
  [B3 flexible head], [`[_ x]`], [any application whose last argument is `x`],
  [B4 type-driven], [`[unkeyed x]`], [any subterm of the type of `x`],
  table.cell(colspan: 3)[*C. Contextual patterns*: describe where the subterm is],
  [C1 context], [`[X in C]`], [the `X` part of the first instance of `C`],
  [C2 redex in context], [`[t in X in C]`], [the first instance of `t` inside the `X` part of `C`],
  [C3 redex as context], [`[t as X in C]`], [the `X` part of the first instance of `C` with `t` at `X`],
  table.cell(colspan: 3)[*D. Rewrite-only*: the redex is inferred from the rule],
  [D1], [`[in C]`], [the first redex of the rule inside `C`],
  [D2], [`[in X in C]`], [the first redex of the rule inside the `X` part of `C`],
  table.cell(colspan: 3)[*E. Modifiers*: added to B, C or D],
  [E1 occurrence switch], [`{1 3}`, `{-2}`], [keep a subset of the occurrences],
  [E2 named context], [`RHS`], [an abbreviation of an `X in C` part],
)

Two of the C forms look alike but are matched differently. In C2, `[t in X in C]`,
the context `C` is matched first, then `t` is looked for inside its `X` part. In
C3, `[t as X in C]`, the single term `C` with `t` at `X` is matched in one step.

*Nesting.* ssreflect nests at most once: C2, `[t in X in C]`, looks for a redex
inside the `X` part of a context. Deeper forms are rejected:
`[X in Y in f a Y]` fails (`X` is read as a redex), and
`[t in X in _ in Y in C]` does not parse. Contexts compose by substitution,
`C1[C2/X]`, but this does *not* mean the same thing as searching `C2` inside the
`X` of `C1`. In `f a 1 + f b (g 2) = 0`, `(g _ in X in f _ X)` fails, because
the first `f _ _` is `f a 1`, while `(Y in f _ (g Y))` gives `2`. The algebra of
selectors (next note) states when the two coincide.

= One goal, all the kinds

The goal (the paper's Example 8, on `nat`, with `f : nat -> nat -> nat`):

```coq
f (a + b) (2 * (a + c)) + (c + d) + f a (c + d) = 0
```

The target is the last `c + d`, the second argument of `f a`:

#align(center)[`f (a + b) (2 * (a + c)) + (c + d) + f a `#tgt[`(c + d)`]` = 0`]

Every line below was checked in Rocq 9.1: the pattern is given to `set z := (…)`,
or to `rewrite […]Nat.add_comm` for the D forms, and the goal it leaves is shown.

#table(
  columns: (auto, auto, 1fr, auto),
  inset: 5pt,
  stroke: 0.4pt + luma(180),
  table.header([*kind*], [*selector*], [*goal after `set z := …`*], [*result*]),
  [A1], [`"2.2.2"`], [the path: left side (2), second summand (2), second argument of `f` (2)], [#yes],
  [A2], [`{2}(c + d)`], [`… + (c + d) + f a z = 0`], [#yes],
  [B1], [`[c + d]`], [`… + z + f a z = 0`], [#no(2)],
  [B2], [`[_ + d]`], [`… + z + f a z = 0`], [#no(2)],
  [B3], [`[_ (c + d)]`], [`z + f a (c + d) = 0`: the first application ending with `c + d` is the sum `_ + (c + d)`], [other target],
  [C1], [`[X in f a X]`], [`… + (c + d) + f a z = 0`], [#yes],
  [C1], [`[X in f _ X]`], [`f (a + b) z + … = 0`: the first `f _ _` is the other one], [other target],
  [C2], [`[_ + d in X in f a X]`], [`… + (c + d) + f a z = 0`], [#yes],
  [C3], [`[_ + d as X in f _ X]`], [`… + (c + d) + f a z = 0` (the paper's pattern)], [#yes],
  [D1], [`[in f a _]`], [`… + f a (d + c) = 0` with `Nat.add_comm`], [#yes],
  [D2], [`[in X in f a X]`], [`… + f a (d + c) = 0`], [#yes],
  [D2], [`[in X in f _ X]`], [`f (a + b) (2 * (c + a)) + …`: inside the first `f`], [other target],
  [E1], [`{2}[_ + d]`], [`… + (c + d) + f a z = 0`], [#yes],
  [E2], [`[_ + d in LHS]`], [`… + z + f a z = 0`], [#no(2)],
  [E2], [`[_ + d in SNDA]`], [with `Notation SNDA := (X in f a X)%pattern.`], [#yes],
)

What the table shows:
- *A redex alone (B) is not enough here.* Both copies of `c + d` are the same
  instance, so `[c + d]` and `[_ + d]` take both. Only a context (C, D, E2) or an
  occurrence number (A2, E1) separates them.
- *First instance means first in pre-order.* `[X in f _ X]` and
  `[in X in f _ X]` stop at the first `f`, the one applied to `a + b`.
  `[_ (c + d)]` stops even earlier, at the sum `_ + (c + d)`, which is also an
  application whose last argument is `c + d`.
- *Occurrence numbers work but say nothing.* `{2}(c + d)` points at the right
  place today. If a `c + d` is added in front, it silently points elsewhere,
  whereas `[X in f a X]` keeps its meaning (the paper's Example 2).
- *There are many correct selectors.* `[X in f a X]`, `[_ + d in X in f a X]`,
  `[_ + d as X in f _ X]`, `[in f a _]`… all reach the target. The library
  should say which one is best, and why.

= From a path to a pattern

Proof by pointing gives a path (A1); the line it writes needs a pattern. Our
present translation keeps every node on the path and puts a hole beside it:

```coq
elpi point_to_pattern "2.2.2".   (* [X in _ + f _ X = _] *)
```

That pattern is correct, but it says more than needed: `[X in f a X]` is
enough. Finding the small one is the job of a metric.

*The minimal pattern by anti-unification.* A context `C` with `X` at the target
must match the term around the target, and must not match any earlier subterm
with the same head. Here the only earlier `f _ _` is `f (a + b) (2 * (a + c))`.
Anti-unifying it with `f a (c + d)` gives `f _ _`: they differ at both
arguments. So `C` must keep at least one of them, and keeping `a` is the
smallest choice, which gives `[X in f a X]`. In general this is a smallest hitting
set over the places where the target differs from each earlier competitor.

= Selectors and anti-unification

Patterns are ordered by generality: `p ⊑ t` when `t` is an instance of `p`. The
_least general generalization_ `lgg(t, s)` is the most precise pattern that
covers both `t` and `s`. Its holes are the places where `t` and `s` differ.

*The right place.* `⟨p⟩` finds `t` first when `p ⊑ t` and, for every earlier
subterm `s` with the same key, `p` does not cover `s`. Since `p` covers `t`,
covering `s` too means being a generalization of `lgg(t, s)`. So `p` must keep,
from `t`, at least one place where `t` and `s` differ, for every such `s`. The
smallest such `p` comes from a smallest hitting set over these places.
Anti-unification is used negatively here: it says what must not be generalized
away.

*Univocality.* `⟨p⟩` takes all the copies of its first instance `i`. A copy `u`
is a subterm with no place of difference: `lgg(i, u) = i`. So `⟨p⟩` is univocal
exactly when no other subterm `u` has `lgg(i, u) = i`. This depends on the
instance found, not on `p`: in our goal `c + d` occurs twice, so every B
pattern that finds it takes both. A context separates the copies. Climb from
the target and from each copy to their ancestors at the same height. As soon as
the `lgg` of these ancestors has a place of difference, the copies are
separated. Here `f a (c + d)` and `_ + (c + d)` already differ by their heads,
so `[X in f a X]` is univocal. At worst the common ancestor separates them. An
occurrence number `#` is the other way out: always univocal, but it relies on
nothing in the shape of the goal.

#table(
  columns: (auto, auto, 1fr),
  inset: 5pt,
  stroke: 0.4pt + luma(180),
  table.header([*question*], [*against*], [*criterion*]),
  [right place], [earlier subterms with the same key], [keep one difference with each `lgg(t, s)`],
  [univocal], [exact copies of the instance], [no `u` with `lgg(t, u) = t`; otherwise climb until the ancestors differ],
  [robust], [later subterms], [how many differences separate `t` from each later one],
)

*Nesting.* For `⟨C | X⟩ ; ⟨t⟩` (C2) there are two problems. `C` is solved against
the competitors in the whole goal, and `t` only against those inside the `X`
part. Fewer competitors give a smaller `t`. Flattening into `⟨C[t/X] | Y⟩`
brings back all the competitors of the goal, which is the side condition of
law 3.

= Related work

Computer science has had to name places inside tree-shaped expressions again
and again:
- in the 1960s Gorn gave tree addresses;
- rewriting theory turned them into _positions_ (occurrences), written in Dewey
  decimal notation;
- structure editors and proof by pointing turned a mouse selection into a path;
- XML gave XPath location paths, and web testing looks for locators that
  survive changes to the page;
- proof assistants went from occurrence numbers and paths to patterns: Matita,
  ssreflect, Isabelle, Lean's `conv`. A context with a hole, `[X in C]`, names a
  position by abstraction.

Choosing the best name among many correct ones is a generalization problem.
That is the setting of Plotkin's least general generalization and of Mitchell's
version spaces.

*Positions in terms.*
- Gorn, _Handling the growth by definition of mechanical languages_ (AFIPS
  1967; first presented in 1965) defines _tree addresses_ and tree domains.
  These are our paths.
- Dershowitz and Jouannaud, _Rewrite systems_ (Handbook of TCS, vol. B, 1990):
  a position "may be represented — in Dewey decimal notation — as a sequence of
  positive integers", and "positions are often called occurrences". They cite
  Gorn 1967.
- Boudol, _Computational semantics of term rewriting systems_ (1985): positions
  in rewriting. It is cited by proof by pointing.

*Selection in editors and proof by pointing.*
- Grundy, _Window inference in the HOL system_ (1991): focusing a proof on a
  subterm.
- The Centaur system (INRIA, manual 1993): an environment built on structure
  editing.
- Bertot, Kahn and Théry, _Proof by pointing_ (TACS 1994). The user selects a
  subexpression, and the proof step is built by induction on the depth of the
  selection. The name comes from Ritchie's thesis (Edinburgh, 1988), which
  allowed only selections at depth 1 or 2. Proof by pointing cites Boudol,
  Centaur and Grundy.
- Padovani's MathML rendering (thesis, 2003) offers visual selection "in the
  style of" proof by pointing.
- Chaudhuri, _Subformula linking as an interaction method_ (ITP 2013).
- Donato's thesis (Institut Polytechnique de Paris, 2024) proposes
  _Proof-by-Action_. It combines pointing (proof by pointing) with linking
  (drag-and-drop between subformulas), on deep inference, and implements it in
  Actema, which is connected to Coq, and in the Flower Prover.

*Patterns in proof assistants.*
- Wenzel, _Isar_ (TPHOLs 1999). Isabelle's `subst` uses a term pattern plus
  occurrence numbers.
- Coq's `pattern` command (Bertot and Castéran, _Coq'Art_, 2004, §6.3.3).
- Asperti, Sacerdoti Coen, Tassi and Zacchiroli, _User interaction with the
  Matita proof assistant_ (JAR 2007), §3.2. Its patterns are the textual form of
  selections made with the mouse. It cites proof by pointing and CtCoq.
- Gonthier and Tassi, _A language of patterns for subterm selection_ (ITP 2012):
  patterns instead of occurrence numbers. They find Matita's paths "quite
  verbose and not very readable". They cite proof by pointing, Matita, Padovani,
  Coq's `pattern` and Isabelle's `subst`.
- Noschinski and Traut, _Pattern-based subterm selection in Isabelle_ (Isabelle
  Workshop 2014, arXiv:2111.04082). Their language is inspired by Gonthier and
  Tassi's, and its positions are built from conversions. They cite Gonthier and
  Tassi, and Grundy.
- Lean 4's `conv` gives paths (`arg i`, `enter [...]`), and `pattern` gives
  occurrence numbers.

*Anti-unification.*
- Plotkin, _A note on inductive generalization_, and Reynolds, _Transformational
  systems and the algebraic structure of atomic formulas_ (both in Machine
  Intelligence 5, 1970): the least general generalization.
- Huet's thèse d'État (1976): an early algorithm.
- Pfenning, _Unification and anti-unification in the calculus of constructions_
  (LICS 1991): the higher-order case, with binders.
- Cerna and Kutsia, _Anti-unification and generalization: a survey_ (IJCAI
  2023). A generalization problem is a _base relation_ plus a _preference
  relation_. Our metric is such a preference relation.

*Learning from positive and negative examples.*
- Winston, _Learning structural descriptions from examples_ (MIT, 1970).
- Mitchell, _Version spaces: a candidate elimination approach to rule learning_
  (IJCAI 1977), then _An analysis of generalization as a search problem_ (IJCAI
  1979), which cites Plotkin 1970 for the general-to-specific ordering.
- The patterns that cover the target and none of its earlier competitors form a
  version space. Its general boundary is the set of our best patterns.
- Raza, Gulwani and Milic-Frayling, _Programming by example using least general
  generalizations_ (AAAI 2014): lgg as a tool for building programs.

*Robust locators on the web.*
- XPath 1.0 (W3C, 1999): location paths built from steps.
- Myllymaki and Jackson, _Robust web data extraction with XML path expressions_
  (IBM, 2002), and Abe and Hori, _Robust pointing by XPath language_ (SAINT
  2003).
- Montoto et al., _Automated browsing in Ajax websites_ (DKE 2011).
- Leotta, Stocco, Ricca and Tonella, ROBULA (2014) and ROBULA+ (J. Softw. Evol.
  Process 2016). They start from the most general XPath and specialize it until
  it is unique. Their criterion is robustness to changes of the page, which is
  our fragility.

*What connects them.* Proof by pointing cites rewriting (Boudol) and editors
(Centaur, Grundy). Matita, Gonthier–Tassi and Donato cite proof by
pointing, and Noschinski–Traut cite Gonthier–Tassi. Dershowitz–Jouannaud cite
Gorn. Mitchell cites Plotkin, and the anti-unification survey cites Mitchell.
We found no citation linking web locators to proof assistants or to rewriting:
that link is made here.

= The tools (in progress)

- `pattern_select` takes a goal and a pattern. It returns the positions the
  pattern denotes, as computed by our Elpi reimplementation of ssreflect's
  matching (checked against ssreflect by differential tests), and says whether they are
  univocal. It also returns the later instances, which the pattern would select
  if the goal changed before them.
- `select_all` takes a goal and a path. It lists the selectors of each kind that
  denote exactly that position, checked by `pattern_select`, best first.
