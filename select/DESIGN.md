# Selecting subterms: a library of selectors (design, draft)

Starting point: Gonthier–Tassi, *A language of patterns for subterm selection*
(ITP 2012, ~/claudeExp/cl.pdf) and our path library (coq_tmp
`subterm_pattern.v`).

## 1. What a selector denotes

A selector denotes a **set of positions** of the goal (paths), not one
position. In ssreflect, `[t]` denotes *all the occurrences of the first
instance* of `t` (pre-order, keyed matching): `[_ - b]` in
`(a - b) + (b - c) = (a - b) + (d - b)` denotes both `(a - b)` (paper, Ex. 5).

So the basic operation of the library is

    denote : goal -> selector -> set of paths

and a selector is *correct* for a target set S when `denote g sel = S`.

## 2. The botany (the kinds of selectors)

| kind | example | denotes |
|---|---|---|
| path | `"2.3.1"` | one position |
| occurrence | `{2}(a + b)` | the 2nd occurrence of a fully given term |
| term pattern | `[_ - a]` | all occurrences of the first instance |
| context | `[X in snd (_, X)]` | the X-subterm of the first instance of the context |
| redex in context | `[_ + b in X in _ = X]` | first instance of the redex inside the X part |
| redex as context | `[_ + d as X in f _ X]` | the context with the redex put at X |
| named context | `[in RHS]`, `RHS := (X in _ = X)` | a reusable context |
| rewrite-only | `[in X in f _ X]` | redex inferred from the rewrite rule |
| occurrence switch | `{1 3}[t]`, `{-2}[t]` | a subset of the occurrences |

Each kind is a constructor of one Elpi type `selector`.

## 3. Translators

- **path → selector** of each kind, when one exists (today: path → `[X in C]`).
- **selector → paths** (`denote`), following ssreflect's semantics: keyed
  matching (the head constant must be equal verbatim), pre-order, first
  instance, then all its occurrences (arguments compared up to conversion).
- `denote` is an Elpi reimplementation of ssreflect's matching for the
  fragment the library produces (`subterm_select.v`, section "The semantics
  of the patterns", after the paper §2.1–§3 and `ssrmatching.ml`). The
  library runs no tactic. It is checked against ssreflect itself by
  differential tests (`tests/`): generated `.v` files where
  `set z := (<pattern>)` is written literally.

Round-trip tests: for every position (or set) of a corpus of goals, every
kind's translation must denote exactly that set.

## 4. The metric: which selector is "best"

A correct selector should say as little as possible, so that it survives
unrelated changes of the goal (paper, Ex. 2), and say it locally.

**Anti-unification gives the minimal redex.** To select a target subterm `t`
with a term pattern, the pattern must match `t` and no earlier subterm with
the same key (pre-order). For each earlier competitor `c`, anti-unification
`lgg(t, c)` gives the positions where `t` and `c` differ. A pattern
(a generalization of `t`) selects `t` exactly when it keeps, for each
competitor, at least one of those positions. The best pattern keeps the
**fewest** symbols: a minimum hitting set over the disagreement positions
(small in practice; exact search, greedy beyond a bound).

The same applies to the context `C` of `[X in C]`: generalize the enclosing
term, keeping just enough to beat the earlier instances of its key.

**Order of the metric** (to be decided):
1. correct (denotes exactly the target set);
2. no occurrence number (fragile when the goal changes);
3. fewest kept symbols (the anti-unification minimum);
4. smallest context (closest enclosing term);
5. no type annotation;
6. shortest text.

## 5. Library shape

- `subterm_select.v` (Elpi): the `selector` type, `denote`, the
  translators, `lgg`, the metric, `best : goal -> set of paths -> selector`.
- Built on `subterm_pattern.v` (paths, printing, names, checking).
- Commands: `elpi pattern_select "[_ - a]"` (what a pattern denotes, univocal or
  not, its later instances), `elpi select_all "2.3.1"` (every kind, with its
  cost, best first).
- Tests: the paper's examples 1–9 as goals, our path tests, and a
  round-trip over all positions of the test goals; the differential tests
  against ssreflect (`tests/`).

## Open questions

1. The order of the metric (section 4).
2. Selectors as sets: do we support selecting several positions at once
   (all occurrences), or only one position plus "and its other occurrences"?
3. Oracle: decided (user, 2026-11-26): our own Elpi implementation of the
   matching, checked against ssreflect by differential tests.
