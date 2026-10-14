# RADCAN in Rocq

A reflective Rocq/mathcomp tactic, `radcan`, that proves equalities between
expressions built from numbers, variables, `+ − × /`, powers and n-th roots.
It is inspired by the RADCAN algorithm of Caviness and Fateman,
*Simplification of Radical Expressions* (SYMSAC 1976); a transcription of the
paper is in [`radcan.md`](radcan.md).

```coq
Lemma ex1 : sqrt 12 - sqrt 3 = sqrt 3.
Proof. radcan_Rstd. radcan. Qed.

Lemma ex2 (x : R) : 1 < x -> sqrt (x ^ 2 - 1) / sqrt (x - 1) = sqrt (x + 1).
Proof. move=> h. radcan_Rstd. radcan. radcan_Rstd_back. lra. Qed.
(* radcan leaves the side condition 1 < x *)
```

## What it does

- **Fields.** It works on any mathcomp `numFieldType` equipped with a root
  function (`posroot`): real closed fields (`rootR`), ℂ (`n.-root`), and the
  real numbers of the Rocq standard library (`sqrt`, through `Rstruct.v`,
  borrowed from mathcomp-analysis).
- **Normal forms.** Both sides are reified and normalised by a function
  computed with `vm_compute`, and the normal forms are compared. The
  soundness of the normaliser is proved once. Factorisations, gcds and
  inverses are computed without proof and then *checked* by multiplication.
- **Side conditions.** Simplifications that are only true under a condition
  are recorded and left as goals, refined into a readable form: for example
  `√(x²) = x` needs `0 ≤ x`, and `x / x = 1` needs `x ≠ 0`. `radcan_raw`
  leaves the raw conditions instead.
- **Rationalisation.** Denominators are rationalised, including ones that mix
  variables and roots: `(x − y)/(√x + √y) = √x − √y`.
- **Negative numbers under roots.** On ℝ, odd roots of negative numbers are
  handled (`∛(−8) = −2`); on ℂ they go through roots of unity
  (`√(−4) = 2·√(−1)`).
- **Number backends.** Coefficients use Stdlib `Z`/`Q` by default
  (axiom-free proofs). `radcan_big` uses Bignums `BigZ`/`BigQ`, which is
  faster on large numbers.
- **Completeness.** It is not a goal: when `radcan` fails, the equality may
  still be true.

## Building

Requires Rocq 9.1, mathcomp 2.5 (boot, order, algebra, field) and Bignums.

```sh
cd rocq
rocq makefile -f _CoqProject -o Makefile   # once
make -j4
../tutorial/check.sh                       # compiles every tutorial script
```

## Documentation

- [`TUTORIAL.md`](TUTORIAL.md) explains each layer with small Rocq scripts.
  The scripts are in [`tutorial/`](tutorial/) and are checked by
  `tutorial/check.sh`.
- [`PLAN.md`](PLAN.md) records the design decisions, the milestones and the
  roadmap.
- `rocq/Examples.v` contains normaliser examples with timings.

## Files

| File | Content |
|---|---|
| `PosRoot.v`, `PosRootFacts.v` | root interfaces `posroot`, `oddroot`, `negroot` and their lemmas |
| `RootC.v`, `RootR.v` | instances for ℂ and real closed fields |
| `Rstruct.v`, `RootRstd.v` | Stdlib reals as a real closed field; rewriting between Stdlib and mathcomp notation |
| `Syntax.v` | reified expressions, interpretation, side conditions |
| `Backend.v`, `BigBackend.v` | number interface; Z/Q and BigZ/BigQ instances |
| `Mono.v`, `NF.v`, `Factor.v`, `Poly.v`, `Inverse.v`, `Ratio.v`, `Cond.v` | the normaliser and its soundness |
| `Radcan.v`, `RadcanBig.v` | the two instances of the normaliser |
| `Refine.v`, `OddRoot.v`, `NegRootC.v` | condition refinement, odd roots (ℝ), roots of unity (ℂ) |
| `Tactic.v` | reification and the tactics `radcan`, `radcan_raw` |
| `Examples.v` | normaliser examples with timings |
