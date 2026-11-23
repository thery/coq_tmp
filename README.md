# coq_tmp
Temporary development for Coq

## cyp and xtext

Two tools that relate a written proof and a Rocq proof, revived from old
papers (in development):

- [cyp/](cyp/README.md): **coloured proofs**.  A proof written in Markdown,
  the tree of the 2003 paper (a node per list item or per span
  `[…]{.p}`, its formulas tagged `{.claim}`, `{.hyp}`, ..., its
  justifications `*X*{.just}`, among them the two fixed methods
  `*match*{.just}` and `*induction*{.just}`), is checked node by node with Rocq and
  written back with ✅ / ❌ on each node; what a justification word means
  is declared in the proof's files (`CypJustification "word" := tac.`, or
  `:= rules.` for Elpi rules that choose how a node is proved by the shape
  of its goal; `lia`, `tauto`, ... are declared so in `cyp/vernac/Cyp.v`),
  and links to its declaration in the PDF and the web page; an open goal of a proof in progress (`` `G`{.goal} ``) is not
  tried and left to a Proof block.  cyp always succeeds: what it cannot prove is reported and
  left as named goals for a Proof block.  The checker is written in
  Rocq-Elpi (opam switch `elpi5`); the text may be in any language (cyp
  reads only the tags), its messages are in English, French or Italian.
  A larger case study (a floating-point paper) is kept in a private
  branch.  After *Colouring proofs: a lightweight approach to adding
  formal structure to proofs* (UITP 2003; ENTCS 103, 2004).
  A tutorial with checked examples: [cyp/TUTORIAL.md](cyp/TUTORIAL.md).
- [xtext/](xtext/README.md): **text from proofs**.  A Rocq-Elpi command,
  `ExtractText foo.`, that writes the proof term of `foo` as a coarse but
  faithful text, in ten languages (`in "fr"`): printed as plain text, or
  in cyp's format with `#[tags]` and in a file (`ExtractText foo to
  "foo.md".`); `ExtractText_partial.` does it for a proof in progress,
  its open goals tagged `{.goal}`.
  After Coscoy, Kahn and Théry,
  *Extracting Text from Proofs* (TLCA 1995), and Yann Coscoy's thesis
  (2000): its staged translation (chapters 2-4, up to the named
  intermediate results) and inductive types ([THESIS.md](xtext/THESIS.md)).
- [lexicon/](lexicon/README.md) and [prooftext/](prooftext/README.md): the
  libraries the two tools share, the words of proofs in each language and
  the format of proof texts.
- **The PDF of a proof text**, with Typst: `prooftext/pdf.sh proof.md`, for
  a text written by xtext (also `ExtractText foo to "foo.typ".`) or checked by
  cyp.  The formulas are mathematics (∀ n ∈ ℕ, n + 0 = n; fractions,
  powers, √, |x|), printed from their Rocq terms by a table of notations
  that a library can extend; `--code` keeps the Rocq code, `--html` makes
  an HTML page (MathML) instead of the PDF.  Each role of a formula has its
  own light background and a mark readable without colour (a frame, a
  dashed or dotted line), with a legend at the end; the open goals of a
  proof in progress are framed in the text; a structured text keeps
  its list, a free text its paragraphs (no structure shown, decision 7 of
  the [proposal](proposal/PROPOSAL.md)), and cyp's statuses are coloured
  marks; on the web page, the pointer over a node highlights what it rests
  on (its conclusion, hypotheses, subnodes and the formulas its names point
  to), and the legend's roles are switches that turn their colours on and
  off (a button before them turns them all off, or all on;
  `pdf.sh --roles claim,just` colours only those
  roles); Arabic is laid out from right to left.  The PDF and the page have links: a name (h) and its
  uses lead to the step that introduced it, a lemma of the corelib or the
  stdlib to its documentation, and the pages of the gallery
  (`prooftext/gallery.sh`) to each other
  ([prooftext](prooftext/README.md#the-pdf-of-a-proof-text-typst),
  [links](prooftext/README.md#links),
  [formulas as mathematics](prooftext/README.md#formulas-as-mathematics)).

## elpi-tools

Tools for standalone Elpi 4 (opam switch `elpi5`, not Rocq-Elpi; in
development), in [elpi-tools/](elpi-tools) (how they work and why:
[elpi-tools/DESIGN.md](elpi-tools/DESIGN.md)):

- [reflect/](elpi-tools/reflect/README.md): **a program as data**.
  `elpi-reflect file.elpi` prints the types, constructors, signatures with
  modes, rules (with the place of each premise) and CHR rules of an Elpi program as Elpi facts, for tools
  written in Elpi (Elpi has no `clause/2`).
- [check/](elpi-tools/check/README.md): **property-based testing**.
  Properties written in the program, `property "rev-involutive" (pi L R L2\
  rev L R ==> rev R L2 ==> L2 = L).`, checked by `elpi-check file.elpi` on
  random values generated from the declared types (inputs and outputs from
  the modes), or by a random derivation of a generator predicate; failing
  cases are shrunk (each part, and equal values together).  The random
  values of a property depend only on the seed and its name: the same
  counterexample alone (`-p`), in its file and in VS Code.  With `-json`,
  a report for tools, with the goal that replays the shrunk counterexample
  in the debugger.
- [debug/](elpi-tools/debug/README.md): **a debugger**.  `elpi-debug
  file.elpi 'goal'` runs the goal through a meta-interpreter written in
  Elpi: ports (call, exit, redo, fail, cut, CHR wake-up), the attempts of
  the CHR rules and the constraint store, breakpoints and stepping,
  counts and time per predicate, and on failure the deepest failing goal
  with each clause tried and why it did not apply (or that the predicate
  has no clause at all); the bindings made by each unify step and
  by each call (at its exit); at each call, the premise of the clause it
  comes from (`premise 1 of lists.elpi:16`).  About 20 times slower than the real engine
  on the benchmarks of its README.  Its strategy can be random:
  elpi-check uses it to generate.  Wherever it works around something
  Elpi does not offer (the variables of a term, the trail, CHR hooks, a
  crash, an `Obj.magic` ...), a stand-in sits behind a small interface,
  listed with the API that would remove it in
  [debug/ELPI-FEATURE-REQUESTS.md](elpi-tools/debug/ELPI-FEATURE-REQUESTS.md).
- [dap/](elpi-tools/dap/README.md): **the debugger in VS Code**.  `elpi-dap`,
  a debug adapter (Debug Adapter Protocol) on `elpi-debug -machine`, and a
  small VS Code extension: breakpoints on clause lines and on predicates,
  step in, over, out, continue, pause, restart a call, the stack of calls
  at the goals they come from (the premise highlighted, not the whole
  clause line), four scopes (the goal, the variables of the query by
  their names, the local program, the eigenvariables), watch expressions.
  The same extension shows the properties of elpi-check in the Test
  Explorer (run buttons on their lines, the shrunk
  counterexample on failure, "Debug this counterexample").  Tested by
  scripted DAP sessions and in Node with a stand-in for VS Code, not by
  clicking.
- [demo/](elpi-tools/demo/DEMO.md): **a demo** of the tools, also in VS Code
  ([`demo/.vscode/launch.json`](elpi-tools/demo/.vscode/launch.json)).

Build and test: `cd elpi-tools && dune build && dune build @runtest`.

## pbp: proof by pointing

[pbp.v](pbp.v) is the tactic of *Proof by Pointing Revisited*: `pbp [X in
X /\ _ -> _]` brings the subformula at `X` to the surface of the goal
(rules for `/\`, `\/`, `->`, `~`), and `pbp [X Y in X -> (Y -> _) -> _]`
links two subformulas (proof by linking).  A free variable of the
pattern names the assumption introduced at its place (`[X in Y /\ X ->
_]`), else it is called `pbp`.

[pbp_select.v](pbp_select.v) writes the pbp call from a selection in the
printed goal, for an interface where one selects with the mouse
(tests: [pbp_select_test.v](pbp_select_test.v)):

| goal | selection | `elpi pbp_pattern ...` prints |
|---|---|---|
| `a + b = b + a` | the first `a` | `pbp [X in X + _ = _].` (`0 1`) |
| `a + b = b + a` | the last `a` | `pbp [X in _ = _ + X].` (`6 7`) |
| `A /\ B -> B /\ A` | the last `A` | `pbp [X in _ -> _ /\ X].` (`9 10`) |
| `A /\ B -> A /\ B` | the two `A` | `pbp [X Y in X /\ _ -> Y /\ _].` (`0 1 6 7`) |
| `a + b + c = c` | `b + c` (not a subterm) | `pbp [X in X = _].`, warning: widened to `a + b + c` |
| `forall n : nat, exists m : nat, n + m = m + n` | the first `n + m` | `pbp [X in forall n : nat, exists m : nat, X n m = _].` |
| `B`, with `ab : A -> B` | `B` in `ab`, then `B` | `move: ab; pbp [X Y in (_ -> X) -> Y].` (`ab 3 4 0 1`) |

### The command, for the interface

```
elpi pbp_pattern S E.               (* a range of the conclusion *)
elpi pbp_pattern H S E.             (* a range of the type of hypothesis H *)
elpi pbp_pattern S E S' E'.         (* two selections: linking *)
elpi pbp_pattern H S E S' E'.       (* hypothesis H and the conclusion *)
elpi pbp_pattern H S E H' S' E'.    (* two hypotheses *)
```

- `S E` is a range of the goal as it is displayed (the conclusion, or
  the type of the hypothesis, as coq-lsp's `proof/goals` gives them):
  `S` included, `E` excluded, counting from 0 **only the characters that
  are not blanks** (spaces, tabs, line breaks), each Unicode character
  counting one.  The range then does not depend on the width the goal is
  printed at, its line breaks or its indentation (coq-lsp and
  `coq.term->string` break lines at different places).  An empty range
  (`S = E`) is a click on the character `S`.  In JavaScript:
  `const nb = (s, i) => [...s.slice(0, i)].filter(c => !/\s/.test(c)).length;`
  gives the count for the offset `i` of the displayed string `s`.
- It is a tactic: it is sent after the sentence where the goal is shown
  (as rocq-web's queries are, with `petanque/run_at_point`), prefixed by a
  goal selector for another goal than the first (`2: elpi pbp_pattern 0
  1.`, and the line inserted is then `2: pbp ...`).  The goal is unchanged.
- It prints one message, the line to insert, e.g. `pbp [X in X + _ = _].`
  (a notice).  A selection that is not a subterm (`+ b`, half a name)
  stands for the smallest subterm that contains it, with a warning
  `pbp_pattern: the selection is widened to a + b` (warning
  `pbp-widened`).  A selection in a hypothesis `H` generalizes it: the
  line is `move: H; pbp [...]`.  The errors (`Tactic failure:
  pbp_pattern: ...`): a range outside the printed term, two selections
  one inside the other, a subterm that cannot be abstracted (the type
  `nat` of `forall n : nat, n + 0 = n`), a pattern that does not parse.

### How

The printed goal is matched with the term by Rocq's printer itself: for
each subterm, the goal is printed again with this subterm replaced by a
marker `pbp_mark` whose two arguments (its type and the subterm) are
implicit, so it prints as one word and the binders above it print as
before; what is printed before and after the marker is what is printed
before and after the subterm (up to the parentheses around it).  So the
notations, implicit arguments, coercions and parentheses are those of the
goal, and two occurrences that print alike (the two `a` of `a + b = b +
a`) are told apart by their places.  A subterm that is not printed as a
whole has no range and cannot be selected: the function behind a
notation (`Nat.add` behind `+`), an implicit argument, `S O` inside the
numeral `2`, the head of an application with implicit arguments
(`length` in `length (rev l)`).  The selection is the smallest subterm
whose range contains the range (among subterms with the same range, the
outermost).

The pattern is the goal where the selection is the variable `X` (applied
to the variables bound above it that it uses: `X n m`), where the largest
printed subterms beside the path to the selection are holes `_`, and
where the rest is kept: heads of applications, what is not printed, the
types of dependent binders.  `X`, `Y` are renamed (`X0`, ...) if the goal
uses these names.  The pattern is then checked: its text is parsed and
elaborated again (`coq.parse.argument`), and it must unify with the goal
where the selections are its variables, at their places.

Limits: pbp itself has rules for the logical connectives only (`pbp [X
in X + _ = _]` is a valid pattern, for `rewrite [X in X + _ = _]...` too,
but pbp fails on it); pbp's notation `[X in ...]` clashes with
ListNotations' `[x]`, so with ListNotations imported the pattern does not
parse (an error); a hypothesis that others depend on cannot be
generalized by `move:`; the printing of the goal by coq-lsp and by
`coq.term->string` was compared on the goals of the tests only (equal up
to blanks).
