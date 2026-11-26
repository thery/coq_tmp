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
  - `diff_support.v` holds the Elpi side of these tests.
- `DESIGN.md`, `PATTERNS.md`, `GRAMMAR.md`, `tutorial.typ`: the design notes,
  the kinds of selectors, the algebra of selectors and a tutorial.

## Build and run

From the root of coq_tmp:

    make select/subterm_select.vo select/subterm_select_test.vo
    select/tests/run.sh                       # every corpus
    select/tests/run.sh select/tests/corpus_paper.v
