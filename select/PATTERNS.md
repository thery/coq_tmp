# Patterns for subterm selection (summary of Gonthier–Tassi, ITP 2012)

Source: G. Gonthier, E. Tassi, *A language of patterns for subterm selection*,
ITP 2012, LNCS 7406, pp. 361–376 (hal-00652286; ~/claudeExp/cl.pdf). This note
keeps what concerns designating a subterm: the grammar (§2.1), the matching
order (§2.2), named contexts (§2.3), and matching (§3). Section and example
numbers are the paper's.

## 1. Why patterns (§1, §2)

Two ambiguities when a command acts on part of a goal:
1. *instantiation*: which instance of the rule's left-hand side (`_ + _`);
2. *occurrence*: which copies of that instance.

Instantiating the rule by hand (`addrC (b * c) (-a)`) needs the order or names of
its arguments. Occurrence numbers (`{29}`) are hard to guess, and when the goal
changes they silently point elsewhere (Ex. 2). A pattern says *what the subterm
looks like*, or *where it sits*, so that a broken script fails at once and
locally.

## 2. Grammar (§2.1)

    c-pattern ::= tpat
                | ident in tpat
                | tpat in ident in tpat
                | tpat as ident in tpat
    r-pattern ::= c-pattern
                | in tpat
                | in ident in tpat

`tpat` is a term with holes `_`. *Redex*: the part of the pattern that stands
for the subterm acted on. c-patterns are used by `set`, `elim`, `:`. r-patterns,
the rewrite patterns, add the forms whose redex is inferred from the rewrite
rule.

## 3. Semantics (§2.1)

In every form, "first instance" means the first subterm, in pre-order, that
matches, and "its occurrences" means all the subterms equal to that instance.

| form | redex | subterms affected |
|---|---|---|
| `t` | `t` | all the occurrences of the first instance of `t` |
| `X in C` | the `X` part of `C` | the `X` part of all the occurrences of the first instance of `C` |
| `t in X in C` | `t` | all the occurrences of the first instance of `t` inside the `X` parts of all the occurrences of the first instance of `C` |
| `t as X in C` | `t` | the `X` part of all the occurrences of the first instance of `C[t/X]` |
| `in C` | inferred from the rule | the occurrences of the first instance of the redex inside the first instance of `C` |
| `in X in C` | inferred from the rule | the same, inside the `X` parts of the first instance of `C` |

Examples:
- Ex. 5: `[_ - b]` in `(a - b) + (b - c) = (a - b) + (d - b)` affects **both**
  `(a - b)`.
- Ex. 6: `[X in snd (_, X)]` in `0 = snd (0 * c, 0 * (a + b))` gives
  `0 * (a + b)`.
- Ex. 7: `(_ + b in X in _ = X)` in `a + b = f (a^2 + b) - c` gives `a^2 + b`,
  not `a + b`.
- Ex. 8: `[_ + d as X in f _ X]` in `… + f a (c + d) = 0` gives the last
  `c + d`.

## 4. Matching order (§2.2)

- `t` and `X in t`: every subterm of the goal is matched against `t`.
- `t1 as X in t2`: every subterm is matched against `t2[t1/X]`.
- `t1 in X in t2`: first `t2`; then, inside its `X` part, `t1`.
- `in X in t`, `in t`: first `t`; then the inferred redex inside it.

With `rewrite`, the redex found is then matched against the rule. The order
matters (Ex. 9): in `((_ + _) in X in (_ * X))`, a `_ + _` outside the `X` part
is skipped.

## 5. Named contexts (§2.3)

    Notation RHS := (X in _ = X)%pattern.

A notation stands for an `X in C` part: `(_ + b in RHS)`.

## 6. Matching (§3)

- **Keyed matching.** Matching is tried only on the subterms whose head constant
  is verbatim the head of the pattern (its *key*). The arguments are then
  matched up to conversion. The search is linear in the size of the goal.
- **Two phases** (§3.2). Phase 1 involves no reduction and erases invisible
  arguments (implicit types, casts). Phase 2 is driven by the key, with full
  reduction on the arguments. Without phase 1, `2 * m` could match `m + _` by
  computation (Ex. 10).
- **Occurrences.** Once the instance is fixed, its other occurrences are found
  by key with arguments compared pairwise up to conversion: `1 + (0 + m)` is an
  occurrence of `1 + m`, but `0 + (1 + m)` is not.
- **Special cases** (§3.1):
  - a pattern with no key is an error, unless the type guides the search
    (`unkeyed x`);
  - a key that is a projection matches its canonical instances (`mop` matches
    `cat`);
  - a flexible head (`_ x`) is tried on every subterm.

## 7. Nomenclature (ours)

The ways to designate subterms of a goal, by what they say.

**A. Absolute** (no description of the subterm):
- **A1 path** `"2.3.1"`: one position, the route from the root (pbp, the Rocq
  tags).
- **A2 occurrence** `{k}t`: the k-th occurrence of a fully given term `t`.
- **A3 range**: characters of the printed goal (we derive it from a path).

**B. Redex patterns** (describe the subterm itself):
- **B1 closed term** `[a - b]`: no hole.
- **B2 term with holes** `[_ - b]`, keyed by its head constant.
- **B3 flexible head** `[_ x]`: no key, tried everywhere.
- **B4 type-driven** `[unkeyed x]`: no key, the search follows the type.

**C. Contextual patterns** (describe where the subterm is):
- **C1 context** `[X in C]`: the subterm is the `X` part of `C`.
- **C2 redex in context** `[t in X in C]`: a redex looked for inside the `X`
  part of `C`, which is a two-step context.
- **C3 redex as context** `[t as X in C]`: the context with the redex put at
  `X`, which is a one-step context.

**D. Rewrite-only** (redex inferred from the rule):
- **D1** `[in C]`.
- **D2** `[in X in C]`.

**E. Modifiers** (on any B, C, D):
- **E1 occurrence switch** `{1 3}`, `{-2}`: a subset of the occurrences.
- **E2 named context** `RHS`: an abbreviation of an `X in C`.

What each kind fixes:

| kind | redex | context | first instance | all occurrences |
|---|---|---|---|---|
| A1 | — | — | — | one position |
| A2 | given in full | — | — | k-th only |
| B1–B4 | given | — | of the redex | yes |
| C1 | `X` | given | of `C` | yes (`X` parts) |
| C2 | given | given | of `C`, then of the redex inside | yes |
| C3 | given | given | of `C[t/X]` | yes |
| D1–D2 | inferred | given | of `C`, then of the redex | yes |
| +E1 | | | | the chosen subset |

Our pbp library today produces **C1** only (`[X in C]`, with C as large as the
path).
