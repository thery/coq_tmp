# coq_tmp
Temporary development for Coq

## cyp and xtext

Two tools that relate a written proof and a Rocq proof, revived from old
papers (in development):

- [cyp/](cyp/README.md): **coloured proofs**.  A proof written in Markdown,
  formulas in backticks, is checked step by step with Rocq and written back
  with ✅ / ❌ on each step; Elpi rules choose how each step is proved.
  The checker is written in Rocq-Elpi (opam switch `elpi5`), the text may
  be in English, French or Italian.  A larger case study (a floating-point
  paper) is kept in a private branch.  After *Colouring proofs: a
  lightweight approach to adding formal structure to proofs* (UITP).
- [xtext/](xtext/README.md): **text from proofs**.  A Rocq-Elpi command,
  `Explain foo.`, that writes the proof term of `foo` as a coarse but
  faithful text in cyp's format.  After Coscoy, Kahn and Théry,
  *Extracting Text from Proofs* (TLCA 1995), and Yann Coscoy's thesis
  (2000): its staged translation (chapters 2-4, up to the named
  intermediate results) and inductive types ([THESIS.md](xtext/THESIS.md)).
- [lexicon/](lexicon/README.md) and [prooftext/](prooftext/README.md): the
  libraries the two tools share, the words of proofs in each language and
  the format of proof texts.
- **The PDF of a proof text**, with Typst: `prooftext/pdf.sh proof.md`, for
  a text written by xtext (also `Explain foo to "foo.typ".`) or checked by
  cyp.  The formulas are mathematics (∀ n ∈ ℕ, n + 0 = n; fractions,
  powers, √, |x|), printed from their Rocq terms by a table of notations
  that a library can extend; `--code` keeps the Rocq code, `--html` makes
  an HTML page (MathML) instead of the PDF.  Each role of a formula has its
  own light background and a mark readable without colour (a frame, a
  dashed or dotted line), with a legend at the end; a structured text keeps
  its list, a free text its paragraphs (no structure shown, decision 7 of
  the [proposal](proposal/PROPOSAL.md)), and cyp's statuses are coloured
  marks; on the web page, the pointer over a node highlights what it rests
  on (its conclusion, hypotheses, subnodes and the formulas its names point
  to); Arabic is laid out from right to left.  The PDF and the page have links: a name (h) and its
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
