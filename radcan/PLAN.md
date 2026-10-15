# RADCAN by reflection in Rocq — plan

Source paper: `radcan.md` (Caviness & Fateman, SYMSAC 1976).

## Goal

A reflective tactic that simplifies / proves equalities of unnested radical
expressions, usable on both **ℝ-like** (`rcfType`) and **ℂ-like**
(`numClosedFieldType`) mathcomp structures. **Soundness only** (no
completeness, so §4 irreducibility theorems are not needed).

## Design decisions (2026-10-14)

- Core is generic over `F : numFieldType` plus a `posroot F` record
  (`PosRoot.v`): a root function `proot n a` with three facts, only for
  `0 < n` and `0 <= a`: `proot_ge0`, `prootK` (`proot n a ^+ n = a`),
  `prootM` (`proot n (a*b) = proot n a * proot n b`).
  Restricting to `a >= 0` avoids the inconsistency `1 = √((-1)(-1)) = -1`.
- Instances: ℂ via ssrnum's `n.-root` (`rootC_ge0`, `rootCK`, `rootCMl`);
  ℝ via our own root on `rcfType` built from `poly_ivt`.
- Factorisations computed by the normaliser are **checked, not proved**
  (certificate style): soundness only needs `P = ± ∏ Bᵢ^eᵢ`, verified by
  multiplication.
- Normaliser computes on `Z`/`positive` (fast with `vm_compute`), connected to
  `F` only in the interpretation.
- Stdlib reals: `Rstruct.v` borrowed from mathcomp-analysis (`reals_stdlib`,
  cut after the rcfType instance) + `RootRstd.v` (`radcan_Rstd` rewrites
  `Rplus`/`pow`/`IZR`/`sqrt` into mathcomp form, `sqrt a = rootR 2 a`).
- Tutorial: `TUTORIAL.md`, scripts in `tutorial/`, checked by `tutorial/check.sh`.
- Negative radicands: later (ℝ: odd roots `∛(-a) = -∛a`, even rejected;
  ℂ: roots of unity `ω`).
- Toolchain: switch `native` (Rocq 9.1.1, mathcomp 2.5), ssreflect style.
  rocq-mcp servers: `rocq-radcan` (main session), agent type `rocq-radcan`
  (one private server per agent), launcher `~/rocq-mcp/run-radcan-rocq-mcp.sh`.

## Status (2026-10-14)

M0 and M1 are done: no `Admitted`, and `radcan_eq` is closed under the global context. The tactic `radcan` works on
`posroot` goals, on ℂ (`n.-root`), on rcfType (`rootR`) and on Stdlib `R` (after
`radcan_Rstd`). Tutorial parts 1–6.

Step 1 (variables outside roots) is done: `RVar`, `rinterp r env e`, and normal-form terms of the shape
coefficient × variable monomial × root monomial. Any unrecognised subterm is an atom.
Tutorial part 7.

M2 (division) is done: rational coefficients (`Q`), inverse found by linear algebra and checked by
multiplication, inverse atoms `AInv` as the fallback. Tutorial part 8.

M3 (variables under roots) is done: `RRootE`, a Collins-style basis refined by exact division (checked),
raw conditions `CGe0`/`CNeq0`, `radcan_eq_cond` (with roots) and `radcan_eq_cond0` (root-free, any
numFieldType). The tactic leaves the conditions as goals; on Stdlib R, `radcan_Rstd_back` + `lra`
closes them. `rootR` is 0 on negatives, so `sqrt = rootR 2` holds unconditionally. Tutorial part 9.

## Milestones

- **M0** interface + syntax + interpretation + both instances.
- **M1** integer radicands, `+ - *` (no division): factor radicands, common
  index `L`, normal form = polynomial in `vₚ = proot L p` with `Z`
  coefficients reduced by `vₚ^L → p`; compare normal forms; `norm_sound`;
  tactic on ℝ and ℂ goals. Examples: `√2·√3 = √6`, `(1+√2)^2 = 3+2√2`.
- M2 division (done).
- Step 1 (done): variables outside roots.
- M3 variables under roots. Target example from the user:
  `sqrt(x^2 - 1) / sqrt(x - 1) = sqrt(x + 1)`, true only for `1 < x`: factor the radicand,
  split the root (`0 <= x-1`, `0 <= x+1`), cancel (`sqrt(x-1) != 0`); the tactic must leave `1 < x`.
  General shape: side conditions `0 <= B(x)` and nonzero denominators.
  Decision (2026-10-14): the normaliser returns nf + a list of raw conditions;
  soundness = (all conditions) -> equality; `radcan` leaves them as raw goals
  (`0 <= x - 1`, `x - 1 != 0`, ...). Simplifying them (e.g. into `1 < x`) comes later.

- M4 (done): (0) split Radcan.v (user request): Backend.v, BigBackend.v, Factor.v,
  Mono.v, NF.v, Inverse.v, Cond.v, thin Radcan.v (norm, norm_sound, radcan_eq[_cond]). (a) functorise Radcan.v over a number backend (Module Type: integer and
  rational types, ops, spec lemmas to Stdlib Z/Q); instances Z/Q and Bignums BigZ/BigQ; tactic
  variant to choose; benchmark. (b) faster radicand factoring: bounded trial division by small
  primes + gcd-based coprime basis among radicands (paper form 2 / Collins) + perfect-power test
  (integer k-th root); optional external factor hint. Soundness unaffected (product checked).
  M3 code already routes arithmetic through helpers to prepare (a).
  (c) last: refine the raw side conditions (user request): drop duplicates and trivially true ones
  (0 <= 2, x^2 >= 0 ...), merge e.g. 0 <= x-1, 0 <= x+1, x-1 != 0 into 1 < x where possible;
  the refined set must imply the raw one (proved), raw stays available.

- After M4, easy to hard (user decision 2026-10-14; completeness is NOT a goal):
  - M5 (done) same base under different indices: `√x · ∛x = ⁶√(x⁵)` (merge ARoot atoms over the lcm index).
  - M6 (done) negative radicands: odd roots on ℝ (`∛(−8) = −2`), sign handling of bases
    (`√(1−x)` next to `x−1`).
  - M7 (done) polynomial gcd / square-free factoring of radicands: `√(x²+2x+1) = x+1` given `0 ≤ x+1`;
    univariate first, then multivariate.
  - M8 (done) better condition refinement: several variables, polynomial conditions.
  - M9 (done) roots of unity on ℂ (the paper's ω): `∛(−1)` etc.
  - M10 (done) cleanups found on the way: `x^3/x^3`, `x*x/(x*x)`, `(x^3*y)/(x^3*y)`, `sqrt(x/2 - 1)^2`
    fail (normal forms differ); inverse atoms not rescaled ((2x+2)^-1 vs (x+1)^-1/2).

- Paper examples (`paper/Paper.v`): most of §2 proved; (3) and E misprinted in the paper (refused).
  Main gap found: rationalising denominators mixing variables and roots (paper (1), (3)) -> M11, now proved.
- M11 (done): rationalise denominators mixing variables and roots.
  Method: basis of the root monomials of d (as in M2); the multiplication-by-d matrix has
  polynomial entries; fraction-free Bareiss elimination (exact polynomial division) gives
  u (adjugate column) and E = det with d*u = E, E root-free; E made primitive, gcd(u, E)
  removed (M7); d*u = E CHECKED by normalisation (Bareiss unproved). New lemma:
  d*u = E -> E != 0 -> d^-1 = u * E^-1. Conditions: E != 0 (new) + those of computing d*u.
  Used only as a fallback: radcan_check first tries the current normaliser, then retries
  with mixed denominators rationalised, so existing goals keep their conditions and all
  statements/tactics are unchanged. Dimension cap as in M2. Targets: paper (1), (3)
  (corrected), 1/(1+√x), 1/(x+√2), (√x+√y)/(√x−√y). Split: one agent (Inverse.v, Cond.v,
  Examples.v); main session: tactic tests (F, C, Stdlib R), Paper.v, tutorial part 18.

- M12 (done): combine bounds in the refinement (Refine.v only): 0 <= x-1 and
  0 <= 3-x -> 1 <= x <= 3; drop conditions implied by several refined ones (small
  Fourier-Motzkin on affine conditions, checked).
- M13 (done): absolute values on real fields: sqrt((x-2)^2) =
  |x-2| without condition (even roots of even powers give |B|), in the normaliser.
  Same agent: radicands containing roots are first normalised; if no root is left the
  radicand is treated as usual (paper §2 nested example sqrt(x^2+3x+3+sqrt(x+1)sqrt(x+1))
  = x+2). True denesting (sqrt(3+2sqrt 2) = 1+sqrt 2) stays out of scope (paper excludes it).
  Also: diagnose paper (4)=(6) on C (false for principal roots, or a real gap?).

- After M12/M13 (user go, 2026-10-15):
  - M14 (done) radcan_lra on Stdlib R: radcan_Rstd; radcan; radcan_Rstd_back; try lra on each
    condition, leave only those lra cannot prove (Tactic.v / RootRstd.v, main session).
  - M15 roots given by hypotheses (paper's symbolic reading): symbols y with y ^+ n = B in
    the context are algebraic atoms reduced by the relation; results hold for every choice
    of roots; paper (2) provable in its own sense (with the omega/sqrt 2 relation given).
  - M16 irreducible factorisation of radicands (paper form 1): univariate factoring over Z
    (Zassenhaus/Berlekamp-Hensel or small-degree methods), checked by multiplication;
    sqrt(x^2-1) = sqrt(x-1) sqrt(x+1) even when no factor appears in the goal; multivariate
    later if feasible. Phase 1 DONE: rocq/IrrFactor.v (standalone, Berlekamp mod small p +
    Hensel + Zassenhaus, `ufactor : seq Z -> seq (seq Z)`, not yet in _CoqProject).
    Phase 2 (after M13): plug irr_split into mk_basis in Poly.v as a FALLBACK only (like
    M11), because splitting strengthens conditions (0 <= x-1, 0 <= x+1 instead of
    0 <= x^2-1, which excludes x <= -1).
    Multivariate stages 1-2 DONE: rocq/MFactor.v (standalone, imports IrrFactor; homogeneous
    via dehomogenisation, factors linear in some variable; `mfactor : mpoly -> seq mpoly`).
    Phase 2 plugs both ufactor and mfactor into Poly.v's basis (after sqf, fallback only).
    Stage 3 DONE: MFactorEEZ.v, mfactor_full (Wang-style EEZ, multivariate Hensel lifting).

- M17 (done): radcan_simplify, analogue of ring_simplify: rewrite a term into
  its printed normal form (nf_to_rexpr), conditions as goals; new files Simplify.v,
  SimplifyTac.v, tutorial Tut21 (no edits of existing files while M12/M13 run).

- Splits (user request): Refine.v -> RefPoly/RefCheck/RefHeur/Refine/RefineEx (done);
  Cond.v -> CondSimp/CondRoot/CondNorm/Cond right after M13 and BEFORE M15/M16 phase 2.

- M18 (done): monomial content taken out of denominators (1/(x^2+x) = 1/x * 1/(x+1)),
  in Inverse.v, checked.
- M19 (phase 1 done: Denest.v, radcan_eq_denest; phase 2 = outer pre-pass in Tactic.v fallback after frac, no Cond.v change needed): depth-two square-root denesting (sqrt(3+2 sqrt 2) = 1 + sqrt 2):
  candidate formula (unverified) + verified sign certificate (rational bounds on roots) +
  proot_eq; new file Denest.v; phase 2 = pre-pass in Cond.v after M16 phase 2.

- M20 (done, tactic integration pending: Frac.v into _CoqProject before Tactic.v; radcan falls back to frac_split, see Tut26 radcan_frac_with_gen): roots of fractions, paper rule (i) and eq. (9): sqrt(P/Q) = sqrt P / sqrt Q
  with 0 <= P, 0 <= Q; confirmed missing (fails on cca7649); pre-pass frac_split in new file
  Frac.v + combined theorems; tactic integration (fallback) by the main session.
- Omega: STOP after Ω2 (user decision 2026-10-15); Ω3-Ω7 dropped from the queue. Ω0-Ω1 DONE (OmegaRoot.v smallroot, OmegaC.v rootC_smallroot + rootC_double), Ω2 running (OmegaPass.v pre-pass). Omega plan DONE (plans/OMEGA_PLAN.md): Ω0 root characterisation, Ω1 explicit ω_3/ω_4/ω_6/ω_12, Ω2 normaliser mode (paper (2), Part 16 Fails), Ω3 index law + primitivity (hard, 400-600 lines, UnitArc.v), Ω4 merge, Ω5 certified cyclotomic reduction, Ω6 sqrt2/3/5 table. Recommended Ω0->Ω2 first.

- M19 phase 3 (queued, user go): denesting with variables, sqrt(a + b sqrt c) with a, b, c
  polynomials: a^2 - b^2 c a perfect square in Q[x] (via sqf), candidate sqrt((a+d)/2) +-
  sqrt((a-d)/2), conditions 0 <= (a+-d)/2, sign as condition CGe0 candidate (refinement
  must drop 0 <= 1 + sqrt(x-1): roots are nonnegative). Example sqrt(x + 2 sqrt(x-1)) =
  1 + sqrt(x-1) for 1 <= x.
- M19 phase 4 (queued, user go): several square roots, sqrt(10+2 sqrt 6+2 sqrt 10+2 sqrt 15)
  = sqrt 2 + sqrt 3 + sqrt 5: heuristic search of sqrt p + sqrt q + sqrt r over divisors,
  checked by squaring + sign certificate.
- Integration design (user question 2026-10-15): the pre-passes are COMPOSED, not separate
  fallbacks: prepass = omega_rw o denest_rw o frac_split (order: fractions, denesting, omega),
  iterated to a fixpoint with fuel, soundness = chained lemmas, conditions concatenated;
  radcan = plain check, else prepass + check. New small file Prepass.v + Tactic.v change.
  Test goals needing two passes, e.g. sqrt((3+2 sqrt 2)/x).

- Queue order (2026-10-15): integration batch after M16 phase 2 -> Cond.v split -> M15;
  M19 phase 4 after phase 3 (same file Denest.v).

## Work split for M0+M1

- Agent 1 (roots): `RootC.v`, `RootR.v`, derived lemmas in `PosRootFacts.v`
  (`proot (n*k) a ^+ k = proot n a`, `proot n (a^+n) = a`, `proot n 1 = 1`, …).
- Agent 2 (algorithm): `Syntax.v` (pexpr/rexpr, interpretation),
  `Radcan.v` (normal form, normaliser, `norm_sound`).
- Main session: reification tactic + examples on ℝ and ℂ; coordination.
