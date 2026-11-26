# select: subterm selectors for Rocq/ssreflect

Which subterms of a goal an ssreflect pattern selects, and the reverse:
the patterns (and other selectors) that designate a given subterm. It
follows Gonthier and Tassi, *A language of patterns for subterm selection*
(ITP 2012). Positions are the paths `i.j.k` that Rocq's
`Set Printing Subterm Paths` shows (`../subterm_pattern.v`).

## Files

- `subterm_select.v`: the library (Elpi), with these tactics:
  - `elpi pattern_select ["H"] "<pattern>"`: the positions the pattern
    selects, whether it is univocal, and its later instances;
  - `elpi select_all ["H"] "<path>"`: the ways to designate that position,
    each one checked, best first, with its cost.

  The semantics of the patterns is ssreflect's, reimplemented in Elpi for
  the fragment the library produces (see the file's header). The library
  runs no tactic.
- `subterm_select_test.v`: tests. They cover the paper's examples, the
  selector algebra, and round trips over the goals of `../point_paths_test.v`.
- `tests/`: the differential tests against ssreflect.
  - `run.sh` compiles each `corpus_*.v`. Its `elpi diff_gen` and
    `elpi diff_cases` lines print the cases with the Elpi result.
  - It then writes `gen/<corpus>_ssr.v`, where every case runs
    `set z := (<pattern>)` literally, and compiles it.
  - It prints, per category, the cases that agree or disagree. The report
    is also written to `gen/<corpus>.report`.
  - `diff_support.v` holds the Elpi side of these tests; `random_gen.v` and
    `gen_random.sh` write `corpus_random.v`, random goals with random
    patterns.
- `DESIGN.md`, `PATTERNS.md`, `GRAMMAR.md`, `tutorial.typ`: the design notes,
  the kinds of selectors, the algebra of selectors and a tutorial.

## Build and run

From the root of coq_tmp:

    make select/subterm_select.vo select/subterm_select_test.vo
    select/tests/run.sh                       # every corpus
    select/tests/run.sh select/tests/corpus_paper.v

## Differential tests: results

The corpora are the paper's examples, the goals of `../point_paths_test.v`,
the categories, and 200 random goals (`gen_random.sh 200 42`). The
patterns are the given ones, every pattern of `select_all` and of
`point_to_pattern`, and 12 random ones per random goal. Every case agrees
with `set`, except these known differences:

- **The parameters of a match.** Rocq-Elpi does not show the parameters
  of a match on a parametrised inductive, such as `nat * nat` in
  `let '(a, b) := p in …`. ssreflect visits them, and `set` puts `z` in
  the types of the binders that come from them. The Elpi semantics does
  not see them (3 cases in `corpus_point_paths`).
- **A `let` with holes inside a context.** ssreflect does not match
  `(X in (let x := X in _) = _)`; the Elpi semantics does (1 case in
  `corpus_categories`).

The rewrite-only patterns (`in C`, `in X in C`) and the patterns outside
the supported fragment are reported as such and are not given to `set`.
