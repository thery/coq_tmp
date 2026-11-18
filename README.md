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
