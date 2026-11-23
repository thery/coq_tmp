# Cleaning rounds (branches cleaning-round, cleaning-round-2): review and what was done

A record: the excerpts, predicate names and line numbers below are those
of the code at the time of each commit.  Several of the predicates named
in the tables (`claims-then`, `level`, `step-kind`, `text-elements`,
`nearer-match`, `open-claims`, `scope-ctx`) no longer exist: cyp's
proof.elpi was rewritten for the tree of nodes since.  In "Not done", the
line numbers were replaced by the file names on 2026-11-23 (the names of
the predicates are given).

Scope: cyp (cyp/vernac/elpi, cyp/vernac/*.v, cyp/bin), xtext (xtext/elpi,
xtext/*.v), prooftext/, lexicon/, elpi-tools (reflect, check, debug, dap).
radcan/ and private material left out.  Earlier rounds already done and not
redone here: REVIEW.md (the first review: one cyp in Elpi, shared lexicon,
done since), xtext-clean (1dca77e, 2f4515b: xtext helpers, names by intent,
dead code), elpi-debug's cleaning pass (48cfcbf: one file per concern in
debug/lib), cyp-clean-reader (5c70ace: names of unnamed hypotheses).

First round: not edited, because other branches worked there then: prooftext/typst*.elpi,
the Typst template, gallery.sh (prooftext-links), elpi-tools/debug/lib and
dap/lib (elpi-debug-chr).  Findings there were listed, not implemented; the second round did them
(those branches are merged).

Kinds: duplication across tools (dup-tools), duplication inside a tool
(dup), misplaced code, dead code, unclear names, over-long predicates,
inconsistent conventions, missing comments.

## First round: done (one commit each; outputs identical before and after)

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
| 7 | medium | dup | Cyp.v: three commands listing the same 23 files one per line: one line per library, as ExtractText.v | fbcbfb4 |
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

## Second round (branch cleaning-round-2): done

Same tests for each commit as above (the cyp examples and the texts of
cyp/vernac, the six .v tests, cyp on xtext's 80 texts and on the 108
texts in other languages, xtext's `make all`, prooftext's check.v,
check_maths.v and typst/check.sh), compared with a run before the first
commit: identical, except where said.  elpi-tools: `dune build
@runtest`.

| # | priority | kind | change | commit |
|---|---|---|---|---|
| 10 | high | dup-tools | one reader of the text of a step, `text-parts` / `after-formula` (prooftext/formulas.elpi), for cyp (text.elpi) and the Typst writer | 3ae8ac5 |
| 11 | high | dup-tools | the Dewey number of a step, `step-number` (prooftext/document.elpi), for cyp and the Typst writer | 7810f52 |
| 12 | medium | dup | proof.elpi: `claims-then`/`open-claims` and `exports`/`open-exports` one each, with what follows the claims as a value (`after-claims`); `scope-ctx`/`statement-ctx` one `under-context` | 2d10236 |
| 13 | medium | dup | elpi-tools: one generator of embedded Elpi files, embed/embed.exe, for elpi-check and elpi-debug | 0ce7cf8 |
| 14 | medium | dup | proof.elpi: `hyps` in two clauses (`is-hyp`, `name-after`) | 530714a |
| 15 | low | dup-tools | header fields: `field-value`, `header-lang` (prooftext/header.elpi) for cyp's `field` and language fallback and typst.elpi's two lookups | eafff9e |
| 16 | medium | dup | xtext tests: `expect`, `expect-text`, `after-title` in test-helpers.elpi | f4fd851 |

10. Where the two readers differed, the shared one does this (the
    contract is in prooftext's README, "Reading a proof text"):
    - a class is `{.letters}`, upper case too (typst.elpi's); a class that
      is no role's tag is read and gives no role (cyp left `{.Hyp}` in the
      words);
    - the name after a formula comes after any number of spaces (cyp's;
      typst.elpi wanted exactly one);
    - a name after a tagged hypothesis now names it in cyp:
      `` `A`{.hyp} (ha) `` gave the hypothesis the name `H1`, though cyp's
      README says the name is `ha`.  This is the one change of behaviour:
      the names of the hypotheses in the goals of a Proof block (`ha`
      instead of `H1`).  No output of the tests changed (the names do not
      appear in the checked texts nor in the JSON);
    - a backtick with no other after it is text (Markdown, typst.elpi's);
      cyp made the rest of the text a formula.  No test text has one.

    before (cyp text.elpi, and again in typst.elpi with other regexps):

        tag W R W1 :-
          rex.match "^{[.][a-z]+}" W,
          rex.replace "^{[.]\\([a-z]+\\)}.*" "\\1" W T, prooftext.role-tag R T, !,
          rex.replace "^{[.][a-z]+}" "" W W1.

    after (cyp text.elpi):

        pieces S P :- prooftext.text-parts S Parts, std.map Parts part-piece P.

    Dead code removed with it: cyp's `elements-text`/`element-text`
    (unused), `chars`, `flush`, `last-piece`, `negb`.

12. before (two of each pair):

        claims-then _ _ _ _ [] Own OTac Rest G P Rs :- level Own OTac Rest G P Rs.
        open-claims _ _ _ _ [] Acc Rest Ty Pf N Rs :- open-level Acc Rest Ty Pf N Rs.

    after:

        claims-then _ _ _ _ [] Known A P Rs :- prove-after-claims A Known P Rs.
        prove-after-claims (prove-goal Own OTac Steps G) _ P Rs :- level Own OTac Steps G P Rs.
        prove-after-claims (collect-claims Steps Ty N) Known P Rs :- open-level Known Steps Ty P N Rs.

    Its own test, cyp/vernac/claims_demo.md: every path (several claims,
    claims with sub-steps, scopes with several variables, nested, with
    and without a goal); its checked text, JSON, the goals of a bare Proof
    block (Show Existentials) and the proof term (Set Printing All) are
    identical before and after.

## Not done

### Medium

- **dup-tools: `is-prop`** in cyp (proof.elpi, typecheck + unify with
  Prop) and xtext (kinds.elpi, `typ` + whnf).  Two tests of the same
  notion; neither tool's file is the place, and prooftext is about texts,
  so this needs a decision on where Rocq helpers shared by the tools live.
- **dup-tools: the Ltac of the tactics a text may name.**  Cyp.v defines
  `cyp_N` for each name of prooftext/tactics.elpi; ExtractText.v defines
  `xtext_N` and `xtext_g_N` for the six names it writes.  (Obsolete since
  6143f9a: no tool has a time limit any more, and the two tools run the
  same tactic for each of these names: `bounded_firstorder`, `guarded_lia`
  and `guarded_nia` are shared in prooftext/Tactics.v, the others are
  one-line Ltac definitions written in both files.  A shared table needs
  no per-tool limit now.)
- **unclear names (xtext): short constructors** used everywhere: `it`
  (a line, text-tree.elpi), `prf`/`prfp`, `b`/`bih`, `bk`,
  `ak`, `star`/`nostar`, `kp` (reparse.elpi), `ci` (inductive.elpi),
  `cand`, `wd`/`tx`/`nm`; predicates `tr-p`, `tr.aux`, `tsize`, `eshape`.
  Renaming touches most of xtext; xtext-clean renamed others but not these.
- **missing comments (xtext): 81 predicates** without a comment across
  xtext/elpi (staged.elpi 17, reparse.elpi 13, inductive.elpi 9, ...).
- **dup (elpi-tools): the driver plumbing**, left after a second look:
  what the two mains share is the sequence parse, compile, parse the
  query, compile it, run, about six calls; the rest differs on purpose.
  elpi-check writes its files in a temporary directory, hides the errors
  located in the generated facts and reports errors as JSON with -json;
  elpi-debug has its own parser (to rewrite the CHR rules), compiles an
  AST (the `Obj.magic` of `to_api`) and exits at the first error.  A
  shared module would take the error policy as arguments: no clearer
  than the six calls.
- **inconsistent conventions (cyp): messages** fall back to English twice:
  `msg` (messages.elpi) takes "en" when no language is set and the "en"
  table when a key is missing.  The second is right (English is the
  complete table); the first could be prooftext's `default-lang`, but
  CypQed did not load header.elpi.  (Doable now: CypQed loads it,
  Cyp.v, the accumulate lines of the command CypQed.)
- xtext's `dewey` (transducer.elpi) is a path of integers, not the
  string of `step-number`: a different form, left.

### Low

- dup-tools: cyp/bin/cyp.ml `header` reads the header again, in
  OCaml; it has to (the driver runs before Rocq), but it does not check
  the keys against prooftext's `header-key`.
- cyp `undup` (text.elpi now, command.elpi then; Elpi's std has none: fine as it is).
- missing comments in elpi-tools/check/lib (about 15 predicates: run.elpi
  5, analyse.elpi 4, ...).
- elpi-tools/debug/lib and dap/lib: not reviewed in depth.
- cyp's `*by h*` with the name of a hypothesis is read as a tactic
  ("Ltac1 tactic h not found"), though cyp's README says a name is given
  "for *by h*".  Found while testing item 10; not a cleaning matter.
  (Fixed since, 83a892d: a name of a hypothesis, a claim or a variable
  is given to the method; the form is `*h*{.just}` now.)

No file of the scope is over 1000 lines (the longest: staged.elpi 657,
session.ml 559; on 2026-11-23: staged.elpi 711, session.ml 582).  No Python found in the scope.
