# coq_tmp
Temporary development for Coq

## cyp and xtext

Two tools that relate a written proof and a Rocq proof, revived from old
papers (in development):

- [cyp/](cyp/README.md): **coloured proofs**.  A proof written in Markdown,
  formulas in backticks, is checked step by step with Rocq and written back
  with ✅ / ❌ on each step; Elpi rules choose how each step is proved.
  The checker is written in Rocq-Elpi (opam switch `elpi4`), the text may
  be in English, French or Italian.  A larger case study (a floating-point
  paper) is kept in a private branch.  After *Colouring proofs: a
  lightweight approach to adding formal structure to proofs* (UITP).
- [xtext/](xtext/README.md): **text from proofs**.  A Rocq-Elpi command,
  `Explain foo.`, that writes the proof term of `foo` as a coarse but
  faithful text in cyp's format.  After Coscoy, Kahn and Théry,
  *Extracting Text from Proofs* (TLCA 1995), and Yann Coscoy's thesis
  (2000) for inductive types.
- [lexicon/](lexicon/README.md) and [prooftext/](prooftext/README.md): the
  libraries the two tools share, the words of proofs in each language and
  the format of proof texts.

## elpi-tools

Tools for standalone Elpi 4 (opam switch `elpi5`, not Rocq-Elpi; in
development), in [elpi-tools/](elpi-tools):

- [reflect/](elpi-tools/reflect/README.md): **a program as data**.
  `elpi-reflect file.elpi` prints the types, constructors, signatures with
  modes, rules and CHR rules of an Elpi program as Elpi facts, for tools
  written in Elpi (Elpi has no `clause/2`).
- [check/](elpi-tools/check/README.md): **property-based testing**.
  Properties written in the program, `property "rev-involutive" (pi L R L2\
  rev L R ==> rev R L2 ==> L2 = L).`, checked by `elpi-check file.elpi` on
  random values generated from the declared types (inputs and outputs from
  the modes), or by a random derivation of a generator predicate; failing
  cases are shrunk.
- [debug/](elpi-tools/debug/README.md): **a debugger**.  `elpi-debug
  file.elpi 'goal'` runs the goal through a meta-interpreter written in
  Elpi: ports (call, exit, redo, fail, cut, CHR wake-up), breakpoints and
  stepping, counts and time per predicate, and on failure the deepest
  failing goal with each clause tried and why it did not apply (or that the
  predicate has no clause at all).  50 to 150 times slower than the real
  engine.  Its strategy can be random: elpi-check uses it to generate.

Build and test: `cd elpi-tools && dune build && dune build @runtest`.
