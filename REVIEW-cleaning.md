# Cleaning round (branch cleaning-round): review and what was done

Scope: cyp (cyp/vernac/elpi, cyp/vernac/*.v, cyp/bin), xtext (xtext/elpi,
xtext/*.v), prooftext/, lexicon/, elpi-tools (reflect, check, debug, dap).
radcan/ and private material left out.  Earlier rounds already done and not
redone here: REVIEW.md (the first review: one cyp in Elpi, shared lexicon,
done since), xtext-clean (1dca77e, 2f4515b: xtext helpers, names by intent,
dead code), elpi-debug's cleaning pass (48cfcbf: one file per concern in
debug/lib), cyp-clean-reader (5c70ace: names of unnamed hypotheses).

Not edited, because other branches work there now: prooftext/typst*.elpi,
the Typst template, gallery.sh (prooftext-links), elpi-tools/debug/lib and
dap/lib (elpi-debug-chr).  Findings there are listed, not implemented.

Kinds: duplication across tools (dup-tools), duplication inside a tool
(dup), misplaced code, dead code, unclear names, over-long predicates,
inconsistent conventions, missing comments.

## Done (one commit each; outputs identical before and after)

Tests run for each commit: the cyp examples (`cyp/examples/*.md`, their
checked .md and .cyp.json), the .v tests of cyp/vernac (vc_demo, vc_file,
bare_demo, square_pos, named_v, wrong), cyp on xtext's 80 texts (`cyprun.sh`,
compared with results.tsv and with the checked files of a first run), and
xtext's `make all` (examples/ and examples-typst/ unchanged).  Also, where
the change touched them: cyp on the 108 texts in other languages
(results_langs.tsv), prooftext's check.v, check_maths.v, typst/check.sh,
lexicon/check.v.  elpi-tools was not changed (no `dune build @runtest` needed).

| # | priority | kind | change | commit |
|---|---|---|---|---|
| 1 | high | dup | `under-decl` / `under-def` for the 13 copies of "declare a variable and record its name" (proof.elpi, Cyp.v) | 129f6ed |
| 2 | high | dup | `text-elements`: reading a statement or step, written out 3 times (markdown.elpi:38, :125, command.elpi:38) | 65b7752 |
| 3 | high | dup-tools | cyp's `numbered-free-name` (proof.elpi:298) was prooftext's `numbered-name` (names.elpi:13) clause for clause: cyp loads names.elpi | 865f0c7 |
| 4 | high | dup | text.elpi: `better` and `earlier` the same four clauses on two types: one polymorphic `nearer-match`; `last-piece` by `flush` | a10f5d9 |
| 5 | medium | misplaced code | check.elpi: the last clause of `justify-step` stood after `apply-lemma`/`conclusion-sort`; its comment named `justify Tac G` | e63c375 |
| 6 | medium | inconsistent conventions | default language "en" written in check-file and lemma-lang while prooftext has `default-lang` | 0166715 |
| 7 | medium | dup | Cyp.v: three commands listing the same 23 files one per line: one line per library, as Explain.v | fbcbfb4 |
| 8 | high | dup / over-long predicates | proof.elpi: `level` and `open-level` had the same 20-line chain of nested ifs: `step-kind` decides once, one clause per kind | 823565f |
| 9 | high | missing comments | 58 predicates of cyp, prooftext (not typst.elpi) and lexicon without a comment; 2 stale comments | c489fdd |

Excerpts.

1. before (13 times, proof.elpi):

       coq.name->id Nm DeclaredName, pi x\ (decl x Nm C, name-in-scope DeclaredName) => claims-then S J1 N Tac Cs Own OTac Rest G (P2 x) Rs.

   after:

       under-decl Nm C (x\ claims-then S J1 N Tac Cs Own OTac Rest G (P2 x) Rs).

2. before: `justification T Tac T1, pieces T1 Pc, elements Pc rclaim Es,`
   (3 places); after: `text-elements T Tac Es,`.

3. before: `numbered-free-name Used "H" 1 S` and its 5-line definition;
   after: `prooftext.numbered-name Used "H" 1 S`.

4. before: `better (triple N M R) Acc Acc1` / `earlier (triple N M (triple P A R)) Acc Acc1`
   with two identical definitions; after: `nearer-match` for both,
   `pred nearer-match i:triple int int A, ...`.

8. before (level, and again in open-level):

       claims Es Cs0, claim-terms Cs0 Cs Bad, binders Es Vs, hyps Es Hs,
       if (Bad = [_ | _]) (...)
       (if (Cs = [], (Vs = [_ | _] ; Hs = [_ | _])) (...)
       (if (Cs = []) (...)
       (conj Cs C, if (backward Es) (...) (... if (Ch = []) (...) (...))))).

   after:

       level Own OTac [step I Es Tac Ch | Rest] G P Rs :-
         step-kind Es K, level-step K I Tac Ch Rest Own OTac G P Rs.
       level-step (unparsed M) I _ Ch Rest Own OTac G P [rep I (bad M) | Rs] :- ...
       level-step (opens-scope Vs Hs) ...   level-step comment ...
       level-step (backward-claim C) ...    level-step (forward-claims Cs) ...

   Besides the tests above, a text going through every kind (a comment, a
   formula that does not parse, a backward step inside a scope, claims
   with sub-steps) gave the same checked text and JSON before and after.

Item 9 is comments only.  No dead code was removed in this round (none
found in cyp; xtext's was removed in xtext-clean).

## Not done

### High, deferred (files under other work)

- **dup-tools: the inline syntax of a step is read twice, and the copies
  already differ.**  cyp/vernac/elpi/text.elpi (`pieces`, `tag` :230,
  `formula` :219: formulas, classes, hypothesis names) and
  prooftext/typst.elpi (`text-parts` :231, `formula-class` :247,
  `formula-name` :258).  The class is `[a-z]+` in cyp and `[A-Za-z]+` in
  typst.elpi; the name after a formula is `^ *(h)` in cyp and `^ (h)` in
  typst.elpi.  One reader of the inline syntax belongs in
  prooftext/formulas.elpi (it already has `split-justification` and
  `role-tag`), used by both.  Not done: typst.elpi is under prooftext-links.
- **dup-tools: Dewey numbers.**  `dewey` (cyp markdown.elpi:30) and
  `dewey-number` (prooftext/typst.elpi:140) are the same predicate; the
  Typst writer numbers steps "as cyp numbers them".  It belongs in
  prooftext/document.elpi.  xtext's `dewey` (transducer.elpi:24, a path of
  ints) is a third form.  Not done: typst.elpi.

### Medium

- **dup (cyp proof.elpi): the goal / no-goal pairs remain.**
  `claims-then` (:285) and `open-claims` (:389), `exports` (:455) and
  `open-exports` (:466) differ only in what follows the last claim (prove
  the goal, or add to the claims so far).  A continuation argument would
  make one of each.  Same shape for `scope-ctx` (:322) and `statement-ctx`
  (:490).  Not done: it changes the arity of five predicates; it needs its
  own round of tests on the scope examples.
- **dup (cyp proof.elpi:157): `hyps`** has four clauses, two per element
  form (`elt`, `eltt`), where a test `is-hyp` would give two.
- **dup-tools: `is-prop`** in cyp (proof.elpi:123, typecheck + unify with
  Prop) and xtext (kinds.elpi:23, `typ` + whnf).  Two tests of the same
  notion; neither tool's file is the place, and prooftext is about texts,
  so this needs a decision on where Rocq helpers shared by the tools live.
- **dup-tools: the Ltac of the tactics a text may name.**  Cyp.v defines
  `cyp_N` for each name of prooftext/tactics.elpi; Explain.v defines
  `xtext_g_N` (with time limits) for five of them; only
  `bounded_firstorder` is shared (prooftext/Tactics.v).  The time limits
  differ on purpose (xtext checks a contraction quickly), so a shared table
  would need a per-tool limit.
- **dup (xtext tests): `expect`** is defined three times (selection.v:24,
  subproofs.v:43, implicit_motive.v:29) and `check-text` / `after-title`
  twice (subproofs.v, implicit_motive.v).  A shared test file needs care:
  each test file accumulates into the command Explain, and a file loaded
  twice would give duplicate clauses.
- **unclear names (xtext): short constructors** used everywhere: `it`
  (a line, text-tree.elpi:10), `prf`/`prfp` (:15), `b`/`bih` (:35), `bk`,
  `ak`, `star`/`nostar`, `kp` (reparse.elpi:78), `ci` (inductive.elpi:119),
  `cand`, `wd`/`tx`/`nm`; predicates `tr-p`, `tr.aux`, `tsize`, `eshape`.
  Renaming touches most of xtext; xtext-clean renamed others but not these.
- **missing comments (xtext): 81 predicates** without a comment across
  xtext/elpi (staged.elpi 17, reparse.elpi 13, inductive.elpi 9, ...).
- **dup (elpi-tools): two ways to embed Elpi files in an executable**:
  check/bin/embed.ml (a generator, list of files) and debug/bin/dune
  (`echo` + `cat` per file).  One generator would do for both.  Not done:
  debug/bin/dune is next to the files of elpi-debug-chr.
- **dup (elpi-tools): the driver plumbing** (temporary directory, parse,
  compile, report errors) is written separately in
  check/bin/elpi_check_main.ml and debug/bin/elpi_debug_main.ml, and
  reflect/lib/reflect.ml has its own parse-error handling.
- **inconsistent conventions (cyp): messages** fall back to English twice:
  `msg` (messages.elpi) takes "en" when no language is set and the "en"
  table when a key is missing.  The second is right (English is the
  complete table); the first could be prooftext's `default-lang`, but
  CypQed does not load header.elpi.

### Low

- dup-tools: cyp/bin/cyp.ml `header` (:32) reads the header again, in
  OCaml; it has to (the driver runs before Rocq), but it does not check
  the keys against prooftext's `header-key`.
- cyp command.elpi:23 `undup` (Elpi's std has none: fine as it is);
  text.elpi `negb` likewise.
- cyp markdown.elpi:24 `field` (the value of a header field, "" if none)
  would sit naturally next to `header-key` in prooftext/header.elpi.
- missing comments in elpi-tools/check/lib (about 15 predicates: run.elpi
  5, analyse.elpi 4, ...).
- elpi-tools/debug/lib and dap/lib: not reviewed in depth in this round
  (under elpi-debug-chr; 48cfcbf cleaned debug/lib recently).

No file of the scope is over 1000 lines (the longest: staged.elpi 657,
session.ml 559).  No Python found in the scope.
