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
each subterm s, the goal is printed again with s framed by two markers,
`A s B`, where `A` and `B` are two local variables whose names occur
nowhere in the printed goal (`pbp_mark`, `pbp_end`, or these names with a
number: `marker-names`).  An application of local variables prints alike
under every printing option (Printing All, Implicit), and s stays, so the
binders above it print as before; what is printed before `A` and after
`B` is what is printed before and after the subterm (up to the
parentheses around it).  So the
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
printed subterms beside the path to the selection are holes `_` (printed
through the constant `pbp_hole`, whose arguments are implicit), and
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

A prototype names the selection by its **subterm path** instead (Rocq's
printer tags each printed subterm; branches `path-tags` of Rocq and
`point-paths` here): [POINTING-PATHS.md](POINTING-PATHS.md) explains the
paths, with examples.

### Pointing actions: the protocol for the interfaces

[point_actions.v](point_actions.v) makes the actions offered on a
selection a list declared in Rocq (tests:
[point_actions_test.v](point_actions_test.v)).  An interface does not
know `pbp`: it asks for the list of the actions, shows them as buttons,
and runs the one chosen.  Any loaded file can add actions.  `pbp_pattern`
is kept as it is until the interfaces use this protocol.

A tutorial to step through:
[point_actions_tutorial.v](point_actions_tutorial.v).  It loads
point_actions.v only, so the bar has Point and Link at first.  Part 1
proves three small lemmas with Point and Link only (a conjunction, a
case analysis on a disjunction in a hypothesis, implications).  Part 2
writes two actions in Elpi, step by step, all their code in the file:
`Simplify here` (registered with a constant line, then reading the
`point-in` value, then walking the Rocq term along the selection's path
to build the pattern `[X in ...]`, then a clear error) and `Unfold here`
(the same pattern, plus the constant at the head of the selection).
The bar grows as they are registered (`PointActions` after each
registration shows the list).  Two small tactics of the tutorial,
`show_selection` and `show_pattern`, print what an action is given and
the pattern it builds.  The lines the buttons write are left to the
reader: a comment says what to select and which button to click, and
gives the line after an arrow; the file compiles without any click.
`sh point_actions_tutorial_check.sh` checks, from its own table of the
selections, that these lines (and the errors promised) are the ones
`point_run` gives, that point_actions_more.v's actions of the same names
give the same lines (but on a selection under a binder, which they
handle and the tutorial refuses), that the messages the comments
promise ("prints:") are the ones printed, and that the references
`FILE.v:N` name the right lines.

The actions point_actions.v declares (`Point`, `Link`) and those of
[point_actions_more.v](point_actions_more.v) (the others; the demos and
the tests load it, the tutorial does not):

| action | kind | line | e.g. on `1 + 1 + a = double (1 + a)` |
|---|---|---|---|
| `Point` | point | `{pre:revert}pbp {path:pbp}{post:revert}.` | `pbp [X in X + _ = _].` (`0 3`) |
| `Link` | link | `{pre:revert}pbp {path:pbp}{post:revert}.` | `pbp [X Y in X + _ = double Y].` (`0 3 13 16`) |
| `Simplify here` | point | `{pre:in}rewrite {local:pbp}/={post:in}.` | `rewrite [X in X + _ = _]/=.` (`0 3`: `1 + 1` becomes `2`) |
| `Unfold here` | point | `{pre:in}rewrite {local:pbp}/{head}{post:in}.` | `rewrite [X in _ = X]/double.` (`6 17`) |
| `Name occurrence` | point | `{pre:in}set x := {local:occ}({text}){post:in}.` | `set x := {2}(a).` (`15 16`, the second `a`) |

The actions of kind `show` of
[point_actions_show.v](point_actions_show.v) (loaded by the demos and the
tests): they work in the conclusion, in a hypothesis, under binders (the
subterm typed and printed under the binders crossed, with the names of
the goal display) and, by paths, on a binder name (the variable it
binds: they are declared with `point-action-names`):

| action | shows | e.g. |
|---|---|---|
| `Type of` | `t : T` | `n : nat` (the name `n` of `forall n`) |
| `Check this` | what `Check t` prints: `t`, then `     : T` | `nat` / `     : Set` |
| `Normal form` | `t ⇒ v`, `v` by call by value to the normal form (`eval compute`: `coq.reduction.cbv.norm`) | `double 2 ⇒ 4` |
| `Head normal form` | `t ⇒ v`, `v` the weak head normal form (`coq.reduction.lazy.whd`) | `if true then a else 0 ⇒ a` |
| `Where defined` | the head constant or variable: its full name, its kind (a definition, a lemma or opaque definition, an axiom, an inductive type, a constructor, a hypothesis, a local definition, a variable bound by a forall/fun/let of the goal), its library | `Corelib.Init.Nat.add: a definition, in the library Corelib.Init.Nat` |
| `Unfolds to` | `t ⇒ v`, one step of delta: the body of the head constant applied to the arguments, beta-reduced; an error if it is opaque or not a constant | `double a ⇒ a + a  (...double unfolded)` |

A template action can be of kind `show` too: `PointAction "Say text"
show "the selection is {text}" "..."`.

`Point` and `Link` print exactly what `pbp_pattern` prints.  `Simplify
here`, `Unfold here` and `Name occurrence` change the selected subterm only, in the
conclusion or, for a selection in a hypothesis `H`, in `H` (`rewrite
[X in X + _ = _]/= in H.`).

**1. The list.**  Sent as `pbp_pattern` is (a tactic, after the sentence
where the goals are shown; the goal is unchanged):

```
elpi point_actions.
```

It prints one notice, a JSON array, in the order of the declarations:

```
[{"name":"Point","kind":"point","doc":"pbp: bring ..."},{"name":"Link","kind":"link","doc":"..."},...]
```

`kind` is `point` (the action takes one selection), `link` (two) or
`show` (one selection; what `point_run` prints is then a message to show,
not a line to insert: the interface displays it and inserts nothing; it
is printed exactly as a line is, one notice, possibly on several lines).
A `show` action given two selections fails as the other kinds do (`the
action Type of is of kind show and takes 1 selection(s), not 2`).
`doc` is a sentence for a tooltip (may be `""`).  The list is the same in
every goal (an action that does not apply to a selection fails with a
message when it is run); it changes only when a file that declares
actions is loaded, so it may be asked once per document position.

**2. Running an action.**

```
elpi point_run "Name" S E.             (* kind point: in the conclusion *)
elpi point_run "Name" H S E.           (* in the type of hypothesis H *)
elpi point_run "Name" S E S' E'.       (* kind link: two selections *)
elpi point_run "Name" H S E S' E'.     (* ... in H and in the conclusion *)
elpi point_run "Name" H S E H' S' E'.  (* ... in two hypotheses *)
```

- `"Name"` is the `name` of the list, in double quotes (a `"` in it is
  written `""`, as in any Rocq string).
- The selections are those of `pbp_pattern` (above): `S E` counts the
  characters that are not blanks, `S` included, `E` excluded, an empty
  range is a click.  The first selection is `X` of the pattern, the
  second `Y`.
- The goal: the action runs on the first goal; for the goal `n` (from 1)
  the command is prefixed by `n: ` and so is the line inserted (`2: elpi
  point_run "Point" 0 1.`, then `2: pbp [X in X].`).  The two selections
  of a link are in the same goal.
- The output: zero or more warnings `point_run: the selection is widened
  to T` (warning `pbp-widened`), then one notice, the line to insert,
  e.g. `pbp [X in X + _ = _].`
- The errors: `Tactic failure: point_run: ...`, e.g. `no action
  Rewrite (elpi point_actions lists them)`, `the action Point is of kind
  point and takes 1 selection(s), not 2`, `the range 30 31 is not in the printed term`,
  `the range 3 1 ends before it starts`, `no hypothesis H`, `the two
  selections are the same subterm or one is inside the other`, `the
  selection is not a constant nor an application of a constant` (Unfold
  here on a variable), `the action Never does not apply to the
  selection` (an action that fails without saying why).  The interface
  shows the text after `point_run: `.

**2b. Running an action on paths.**  An interface whose goal display
tags each printed subterm with its path (Rocq's `Set Printing Subterm
Paths`, a prototype in the branch `path-tags` of a Rocq clone: each
subterm's Pp is tagged `path:i.j.k`) sends the path of the selected
subterm instead of a range:

```
elpi point_run_path "Name" "P".          (* kind point: in the conclusion *)
elpi point_run_path "Name" "H" "P".      (* in the type of hypothesis H *)
elpi point_run_path "Name" "P" "P'".     (* kind link: two selections *)
elpi point_run_path "Name" "H" "P" "P'". (* ... in H and in the conclusion *)
elpi point_run_path "Name" "H" "P" "H'" "P'".
```

- A path is `"i.j.k"` (`""` for the whole part), the path of the subterm
  in its part (the conclusion, or the type of `H`), in the immediate
  subterms of `kids` (pbp_select.v): an application `f a1 .. an` has `f`
  at 0 and `ai` at `i`, `forall`/`fun` (arrows, branches and return
  clauses included) the name at 0, the type at 1 and the body at 2, `let`
  the name, the type, the value, the body at 0, 1, 2, 3, a `match` the
  scrutinee at 0, the return type at 1 and its branches from 2 (a branch
  is the `fun` of the arguments of its constructor), a cast the type at
  0 and the term at 1.  A name is not a subterm: a path that ends at a
  name selects its binder, widened with the warning `... (a binder name:
  the whole forall is selected)` (unless the action is declared with
  `point-action-names`, which then gets the path of the name); a path
  through a name is an error (`the path 0.1 goes through a binder
  name`).  On `forall n : nat, n + 0 = n`, `n` is `"0"`, `nat` `"1"`,
  `n + 0` `"2.2"`.  It is the tag of the innermost tagged subterm
  containing the selection.  On `1 + 1 + a = double (1 + a)`, `1 + 1` is
  `"2.1"` (eq's type, not printed, is 1), `1 + a` is `"3.1"`.
- A string that is `""` or starts with a digit is a path, any other a
  hypothesis name, which a path follows.
- The part is not printed again and nothing is counted: the display and
  the selection cannot disagree.  The result is the one of `point_run`
  (the same `point-in` value; the patterns may put a hole at any
  subterm, and are checked as before).
- A subterm that cannot be selected is widened, with the warning of
  `point_run` (`pbp-widened`, `point_run_path: the selection is widened
  to ...`), to the nearest subterm above it that can and that is printed
  as a whole (as `point_run` widens a range): the return type of a match
  and the binders of a branch (the pattern variable `k` of `S k` is
  tagged with the path of its `fun`; `let '(a, b) := p` is a match), a
  subterm whose pattern does not pass the check alone in its part (the
  type of a binder that the rest depends on, `n` under a coercion that
  is not printed: `(n + 1)%Z` is `Z.of_nat n + 1`, the scrutinee of a
  `let '(a, b)`).  There is no warning when the subterm it is widened to
  prints as the selection (the coercion `Z.of_nat n` prints as `n`).
- The binders of a pattern are named as the goal display names them: a
  binder named as a hypothesis keeps its name in the type of a hypothesis
  (`move: H; pbp [X in (forall x : nat, X x) -> _]`) and is renamed in the
  conclusion (`x0`), where Rocq-Elpi prints it `elpi_ctx_entry_3_`.  A
  cast `(n : nat)`, which Rocq-Elpi sees as a `let`, is printed back as a
  cast (`pbp [X in (X : nat) = _]`).  When the pattern does not elaborate because
  a selection is the scrutinee of an `if` (`if X then _ else _`: the
  text alone does not give the type of `X`), `X` is written with its
  type: `pbp [X in (IF X : bool THEN _ ELSE _) = _]` (both methods; never
  when the plain pattern works, as under ssreflect's `if` notation).
- The errors are those of `point_run` (with `point_run_path: `), and `no
  subterm at the path 5`, `not a path: 2.x`.
- Tests: [point_paths_test.v](point_paths_test.v) (`elpi
  point_run_path_expect "Name" Line Ws Sel ...`, Ws as for
  `point_run_expect`), the same lines as `point_run` where both apply.
- The cases: [point_paths_cases.v](point_paths_cases.v), goals with every
  construct and every position of the numbering, in the conclusion and
  in hypotheses (`elpi point_paths_check.` there computes the text of
  every subterm and binder name).  The round trip:
  `opam exec --switch=vsrocq-pathtags -- bash point_paths_roundtrip.sh`
  (the Rocq whose printer tags the paths): for every tag `P` of the
  printed goals, the subterm (or binder name) at `P` must print as the
  tagged text; it prints the counts and fails on a mismatch.

**3. Declaring an action.**  With a template:

```
PointAction "Name it" point "set x := ({text})." "name the selected subterm".
```

The kind is `point`, `link` or `show`; the last string (optional) is the `doc`.
A name is declared once.  The placeholders of the template:

| placeholder | is |
|---|---|
| `{path:M}` | where the selections are, written by the path method `M`, in the goal where the hypotheses of the selections are generalized (for the strategy `revert`) |
| `{local:M}` | the same in the part the selections are in: the conclusion, or the type of their hypothesis (for the strategies `in` and `forward`) |
| `{pre:S}` | what the hypothesis strategy `S` writes before the core of the line |
| `{post:S}` | what it writes after the core (before the final dot) |
| `{head}` | the constant the first selection is, or is an application of |
| `{text}` | the first selected subterm, as printed |
| `{pattern}` `{local}` `{revert}` `{in}` | the former names of `{path:pbp}` `{local:pbp}` `{pre:revert}` `{post:in}`, kept |

The path methods (`PointPaths.` lists them), on the first and the last
`a` of `a + b = b + a` (`0 1`, `6 7`), and on the first `a` of a
hypothesis `H : a + b = b + a` (`H 0 1`), `{path:M}` then `{local:M}`:

| method | `0 1` | `6 7` | `H 0 1` | is |
|---|---|---|---|---|
| `pbp` | `[X in X + _ = _]` | `[X in _ = _ + X]` | `[X in X + _ = _ -> _]`, `[X in X + _ = _]` | pbp's pattern |
| `occ` | `{1}` | `{2}` | `{1}` | ssreflect's occurrences of the selected term (`set x := {2}(a)`, `rewrite {2}[a]...`) |
| `at` | `1` | `2` | `1` | Rocq's (`pattern a at 2`, `unfold ... at`) |
| `path` | `[2, 1]` | `[3, 2]` | `[0, 2, 1]`, `[2, 1]` | the position in the term, for Elpi tools |

- The occurrences count the subterms equal to the selected one, left to
  right in the term (heads before arguments, the type of a binder before
  its body, implicit arguments included); ssreflect's `{n}` and Rocq's
  `at n` count them so on the goals tried (by hand: several `a`, under a
  binder, in a match, an implicit `nat`; in the tests, where the lines
  are run: several `a`, under a binder): the two methods differ only in
  how they write the number.  Two selections of the same term give `{1
  4}` and `1 4`; of different terms, an error; a selection that uses a
  variable bound in the goal (`n` in `forall n, n = a`) has no occurrence
  number (an error).
- `path`: the paths of `kids` (pbp_select.v): in an application the head
  is 0 and the arguments 1, 2, ...;
  in a product or an abstraction the name is 0 (not a subterm), the type
  1 and the body 2; in a let the name 0, the type 1, the value 2, the
  body 3; in a match the matched term 0, the return type 1, the branches
  2, 3, ...; in a cast the type 0 and the term 1.  In the goal with the
  hypothesis `H` generalized (`{path:path}`), `H`'s type is `[1, ...]`
  and the conclusion `[2, ...]`.  Two selections give two lists.

The hypothesis strategies (`PointStrategies.` lists them), for a
selection in the hypothesis `H` (for selections in the conclusion they
write nothing):

| strategy | before | after | e.g. Simplify on `H : 1 + 1 + a = a` (`H 0 3`) |
|---|---|---|---|
| `revert` | `move: H; ` (`move: H H'; ` for two) | | `move: H; rewrite [X in X + _ = _ -> _]/=.` (with `{path:pbp}`) |
| `in` | | ` in H` | `rewrite [X in X + _ = _]/= in H.` |
| `forward` | `have H' := H; ` | ` in H'` | `have H' := H; rewrite [X in X + _ = _]/= in H'.` (`H'0`, ... if `H'` is taken) |

`in` and `forward` need the selections in one hypothesis (an error for
two hypotheses, or a hypothesis and the conclusion); whether the core
can act `in H` is the action's business (a `rewrite`, `set`, `pattern`
can; pbp cannot, so `Point` uses `revert`).

Or in Elpi, for an action that computes its line: a predicate `pred
p i:point-in, o:string` from the selections, resolved to subterms of the
goal, to the line, declared by a clause of `point-action` in the
database `pbp_select.db`:

```
Elpi Accumulate pbp_select.db lp:{{
pred same-text i:point-in, o:string.
same-text In Line :-
  point-text In 0 A, point-text In 1 B,
  (A = B, !, Line = "(* the same text *)" ;
   Line is "(* " ^ A ^ " and " ^ B ^ " *)").
point-action "Compare" link "compare the two selections" same-text.
}}.
```

The predicates on the selections (pbp_select.v) are the ones of the
placeholders: `point-pattern`, `point-revert`, `point-local-pattern`,
`point-in-hyp`, `point-head In I GR`, `point-text In I S` (selection `I`,
from 0), `point-hyps` (the hypotheses of the selections), `point-names`
(all the hypotheses of the goal), and `point-count`; point_actions.v adds
`scope-term Scope In T Ps` (the term and the paths of the selections in
it, for `path-goal` or `path-part`) and `occurrences Scope In Ns`.  An
error is `coq.ltac.fail 0 {msg "..."}` (`msg` adds `point_run: `).

A path method or a strategy is declared in Elpi only (they compute), by a
clause in `pbp_select.db`, e.g. (point_actions_test.v):

```
Elpi Accumulate pbp_select.db lp:{{
pred path-depth i:point-scope, i:point-in, o:string.
path-depth Sc In S :-
  scope-term Sc In _ Ps,
  std.map Ps (p\ s\ sigma N\ std.length p N, s is int_to_string N) Ss,
  std.string.concat " " Ss S.
point-path "depth" "the depth of the selections" path-depth.

pred hyp-copy i:point-in, o:string, o:string.
hyp-copy In Pre "" :-
  point-hyps In Hs,
  (Hs = [], !, Pre = "" ;
   std.map Hs (h\ s\ s is "(" ^ h ^ ")") Cs, std.string.concat " " Cs S,
   Pre is "move: " ^ S ^ "; ").
point-hyp-strategy "copy" "generalize copies of the hypotheses" hyp-copy.
}}.
PointAction "Point (copy)" point "{pre:copy}pbp {path:pbp}{post:copy}.".
```

A template may use only the methods and strategies declared before it.

**4. Seeing the actions.**  For a human reader (not for the interfaces,
which use `elpi point_actions`), the command

```
PointActions.
```

prints, at that point of the file (in a proof or not), the actions in
the order of their declarations: name, kind, where it was declared (the
library and the line, for `PointAction`; an action declared by an Elpi
clause has no recorded place), its template or its Elpi predicate, its
doc:

```
7 pointing action(s):
Point (point), declared in coq_tmp.point_actions, line 503
  template: {pre:revert}pbp {path:pbp}{post:revert}.
  doc: pbp: bring the selected subformula to the surface of the goal
...
Name it (point), declared in coq_tmp.point_actions_test, line 188
  template: set x := ({text}).
  doc: name the selected subterm
Compare (link), declared by an Elpi clause
  Elpi: same-text
  doc: compare the two selections
```

`PointPaths.` and `PointStrategies.` print the path methods and the
hypothesis strategies the same way (name, Elpi predicate, doc).

`elpi point_show Sel ...` (a tactic, selections as for `point_run`)
prints the `point-in` value an action is given for the selections,
field by field, with the printed subterms of each part (`shown P S E
T`): what to look at when writing an action in Elpi.

A goal with a `match` (an `if`) can be pointed at: the subterms of the
match's return type, never printed, are not marked.

Limits: the rewrite actions use ssreflect's `rewrite [X in ...]/=` and
`/c`, which are conversions, so they work under binders too, but a
selection that uses a bound variable is the function `X n` of the
pattern, and simplifying it leaves a `(fun m => ...) n`; the `{head}` is
printed as Rocq prints the constant in the goal's context
(`Init.Nat.add` for `+` when PeanoNat is loaded); the list is not
filtered by the selection.
