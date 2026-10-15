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
Proof. move=> h. radcan_lra. Qed.
(* radcan leaves the side condition 1 < x, closed by lra *)
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
- **Simplification.** `radcan_simplify` rewrites both sides into their normal
  form, e.g. `1/(1+√2)` into `√2 − 1`, leaving the side conditions.
- **Denesting.** `√(3+2√2) = 1+√2`, `√(x + 2√(x−1)) = 1 + √(x−1)`,
  `√(10+2√6+2√10+2√15) = √2+√3+√5`; roots of fractions `√(P/Q) = √P/√Q`.
- **Rationalisation.** Denominators are rationalised, including ones that mix
  variables and roots: `(x − y)/(√x + √y) = √x − √y`.
- **Absolute values and real fields.** On real closed fields (and Stdlib
  reals) `√((x−2)²) = |x−2|` and `∛(−8x³) = −2x` need no condition.
- **Factoring.** Radicands are factored over ℤ, in one or several variables,
  so `√(x²−y²) = √(x−y)·√(x+y)` is found even when no factor appears in the
  goal.
- **Negative numbers under roots.** On ℝ, odd roots of negative numbers are
  handled (`∛(−8) = −2`); on ℂ they go through roots of unity
  `ω_n = n.-root (−1)` (`√(−4) = 2·√(−1)`). Roots of unity of different
  indices are merged (`ω₁₀² = ω₅`) and reduced modulo cyclotomic polynomials
  (`ω₅⁴ − ω₅³ + ω₅² − ω₅ + 1 = 0`), using two facts proved on ℂ without
  trigonometry (`UnitArc.v`): the index law and the primitivity of `ω_n`.
  A small table writes `√2`, `√3`, `√5` with roots of unity.
- **Trigonometry through ℂ.** `cos(π/7) − cos(2π/7) + cos(3π/7) = 1/2`
  (IMO 1963) is proved on the Stdlib reals by going to ℂ and using `radcan`
  (`tutorial/Tut35_imo1963.v`).
- **Number backends.** Coefficients use Stdlib `Z`/`Q` by default
  (axiom-free proofs). `radcan_big` uses Bignums `BigZ`/`BigQ`, which is
  faster on large numbers.
- **Completeness.** It is not a goal: when `radcan` fails, the equality may
  still be true.

## Building

Requires Rocq 9.1, mathcomp 2.5 (boot, order, algebra, field) and Bignums.
`tutorial/Tut35_imo1963.v` (cos(π/7) − cos(2π/7) + cos(3π/7) = 1/2 through ℂ)
also needs `rocq-mathcomp-real-closed`.

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
- [`doc/radcan-note.typ`](doc/radcan-note.typ): a short note (Typst) presenting
  the development; its examples are in `doc/NoteExamples.v`.
- [`plans/mathcomp/nthroot_unity.v`](plans/mathcomp/nthroot_unity.v): the facts
  on `n.-root (−1)` as a standalone mathcomp file, with a draft PR description
  in [`plans/MATHCOMP_PR.md`](plans/MATHCOMP_PR.md).
- `rocq/Examples.v` contains normaliser examples with timings.

## Files

| File | Content |
|---|---|
| `PosRoot.v`, `PosRootFacts.v` | root interfaces `posroot`, `oddroot`, `negroot` and their lemmas |
| `RootC.v`, `RootR.v` | instances for ℂ (`n.-root`) and real closed fields (`rootR`) |
| `RealRoot.v` | `realroot`: real fields with odd roots (absolute values, odd roots of any sign) |
| `Rstruct.v`, `RootRstd.v` | Stdlib `R` as a real closed field (borrowed from mathcomp-analysis); Stdlib ↔ mathcomp rewriting, `radcan_lra` |
| `Syntax.v` | `rexpr`, its interpretation, the conditions `cond` |
| `Backend.v`, `BigBackend.v` | the number interface `NUM`, Z/Q and BigZ/BigQ instances |
| `Mono.v`, `NF.v` | atoms, monomials, normal-form arithmetic |
| `Factor.v` | integer factoring |
| `Frac.v`, `Denest.v`, `OmegaPass.v`, `Prepass.v` | pre-passes (roots of fractions, denesting, values of ω) and their composition |
| `IrrFactor.v`, `MFactor.v`, `MFactorEEZ.v` | polynomial factoring over ℤ: one variable (Berlekamp–Hensel–Zassenhaus), several variables (homogeneous, linear factors, Wang's EEZ) |
| `Poly.v` | polynomial exact division, gcd, square-free factoring, radicand basis |
| `Ratio.v` | rationalisation of denominators with variables and roots |
| `Inverse.v` | inverse by linear algebra, checked |
| `Cond.v` | radicands, cancellation, conditions, modes, `radcan_check` and soundness |
| `Radcan.v`, `RadcanBig.v` | the two instances of the normaliser |
| `RefPoly.v`, `RefCheck.v`, `SignCert.v`, `RefHeur.v`, `Refine.v` | refinement of the conditions: polynomials over atoms, proved checker, sign certificates of constants in roots, unverified heuristics, `refine` and its soundness |
| `OddRoot.v`, `NegRootC.v`, `AbsRoot.v` | theorems for odd roots (ℝ), roots of unity (ℂ), real fields |
| `UnitArc.v`, `RootComp.v` | principal roots of `−1` on ℂ: index law, primitivity, largest real part; `(nk).-root x = n.-root (k.-root x)` |
| `GaussSum.v` | Gauss's theorem on the sign of the quadratic Gauss sum, for every odd `n` |
| `OmegaRoot2.v`, `NegCyc.v`, `CycC.v` | records `cycroot` (index law) and `sqrtroot` (√2, √3, √5 table), theorems, ℂ instances |
| `Cyclo.v`, `CycloC.v`, `CycloTac.v` | cyclotomic reduction: certified `Φ`, record `cycprim`, ℂ instance |
| `CycloInv.v` | inverses of sums of roots of unity modulo `Φ`, checked |
| `OmegaRoot.v`, `OmegaC.v` | explicit values of small roots of unity |
| `Dispatch.v` | one checker `radcan_check_shape` and one soundness theorem (raw, refined, with pre-pass) over a record of root facts found by typeclass resolution; adding a mode only touches this file (recipe in its header) |
| `Tactic.v` | reification and the tactics `radcan`, `radcan_raw` |
| `Simplify.v`, `SimplifyTac.v` | printing normal forms back; `radcan_simplify` |
| `Examples.v`, `RefineEx.v` | examples with timings |
