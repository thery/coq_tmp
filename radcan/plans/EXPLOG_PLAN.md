# Exponentials and logarithms: a generic procedure (plan)

Status: plan, revised 2026-10-15 after reading Epstein–Caviness, *Elementary
Proofs of Algebraic Relationships for the Exponential and Logarithm
Functions*, TR223, Wisconsin 1974 (transcribed in `TR223.md`). The user asked
for the generic algorithm given by the theory, not code tuned to examples
(the first prototypes in `explog/ExpLog{,Exp,Ln,Hyp}.v` are kept only as
tests and as a source of tactic pieces).

---------------------------------------------------------------------------

## 0. The theorem we implement

TR223, Theorem 5.7 (Structure Theorem). Let `F_m = F_0(θ_1,…,θ_m)` be a
regular Liouville extension, `θ_j = log A_j` (j ∈ L) or `θ_j = exp A_j`
(j ∈ E).

* (a) `log A_{m+1}` is a new transcendental (a "regular monomial") iff
  `{θ_j}_{j∈E} ∪ {A_j}_{j∈L} ∪ {A_{m+1}}` is multiplicatively independent up
  to constants. Otherwise `A_{m+1} = c · Π_{j∈L} A_j^{p_j} · Π_{j∈E} θ_j^{q_j}`
  with rational `p_j, q_j` (proof of 5.7(a)).
* (b) `exp A_{m+1}` is new iff `{θ_j}_{j∈L} ∪ {A_j}_{j∈E} ∪ {A_{m+1}}` is
  linearly independent over ℚ up to constants. Otherwise
  `A_{m+1} = c + Σ_{j∈L} r_j θ_j + Σ_{j∈E} s_j A_j` with rational `r_j, s_j`.

So: once every `exp` and `log` is rewritten through these relations, the
remaining ones are algebraically independent letters, and the zero test is
rational-function (here: radcan) arithmetic on them.

What we prove in Rocq is only the direction we need: each rewrite is an
equality proved in Rocq (soundness). The search for the relations is
computed and not proved. The independence part of the theorem (needed to say
"different") is not formalised; radcan never claims it.

---------------------------------------------------------------------------

## 1. Setting

Equalities on Stdlib `R`. Functions: `exp`, `ln`; `cosh`, `sinh`, `tanh`,
`Rpower`, `Rlog` are unfolded into them first (no special treatment). `sqrt`
and radcan's roots may occur; inside arguments they are treated as opaque
atoms. `cos`, `sin`, `tan` may occur: the final zero test is then
`radcan_trig` (exp/ln letters are letters there too); by Theorem 5.7(b) over
ℂ, `e^x` and `e^{ix}` are independent, so keeping them separate is right.

Constants: the theorem works over a fixed constant field (ℚ here). `ln 2`,
`exp 1` are new *constants*, outside the theorem. We only use integer
factoring for them (`ln 12 = 2 ln 2 + ln 3`, `exp (c) = exp (1/d)^k`); any
other relation between constants fails.

---------------------------------------------------------------------------

## 2. The procedure

Innermost first: the arguments of the `exp`/`ln` terms of one level contain
only variables, numerals, roots, and letters of the lower levels.

### 2.1 Logarithms (Theorem 5.7(a))

For each `ln A` of the level:

1. Domain: rewrite `ln A = ln |A|` under the condition `0 < A` (Stdlib's
   `ln` is junk on `A <= 0`; this is the only domain condition per `ln`).
2. Factor `A`: reify it as an integer polynomial in the atoms (variables,
   roots, letters; an `exp` letter is an atom) with rational content, factor
   with radcan's unverified `MFactorEEZ.mfactor_full` (integer content by
   `zprimes`). Write `A = c · Π p_i^{e_i}` with `p_i` irreducible and
   primitive, `c` rational, `e_i` integers (negative for a denominator).
3. Check `A = c · Π p_i^{e_i}` with `field` (conditions: denominators
   `≠ 0`), rewrite.
4. Split with `|a b| = |a| |b|`: `ln |A| = ln |c| + Σ e_i ln |p_i|`;
   conditions `p_i ≠ 0` only (no sign assumption on the factors).
   `ln |exp B| = B`; `ln |c|` → Σ over the primes of `c`.
5. The letters of the level are the `ln |p_i|` (one per distinct irreducible
   `p_i`, sign-normalised so that `p` and `-p` give the same letter).

### 2.2 Exponentials (Theorem 5.7(b))

Let `A_1,…,A_k` be the arguments of the `exp` terms of the level and
`ℓ_1,…,ℓ_r` the `ln` letters (2.1) and lower-level `ln` letters.

1. Reify each `A_j` as a rational function `P_j / Q_j` (integer polynomials
   in the atoms, the `ℓ_i` being atoms).
2. Linear algebra over ℚ: with `D = lcm(Q_j)`, the vectors of coefficients of
   `D · A_j`, `D · ℓ_i`, `D · 1` (one coordinate per monomial). Gaussian
   elimination (exact rationals; reuse `Inverse.v`'s `gauss` or write the
   small ℚ version) gives, in order `1, ℓ_1…ℓ_r, A_1…A_k`, a basis
   and for every `A_j` not in the basis
   `A_j = c_j + Σ r_{ji} ℓ_i + Σ_{b basis} s_{jb} A_b` (rationals).
3. Letters: for each basis argument `A_b`, `d_b` = lcm of the denominators
   of the `s_{jb}` (1 if none): letter `E_b = exp (A_b / d_b)`; and
   `exp A_b = E_b ^ d_b`. Constants: `exp c = exp (1/d)^{c d}`.
4. Check each relation `A_j = c_j + Σ r ℓ + Σ s A_b` with `field`
   (conditions: denominators `≠ 0`), then rewrite
   `exp A_j = exp(1/d)^{…} · Π |p_i|^{r_{ji}} · Π E_b^{s_{jb} d_b}`, using
   `exp (r ln |p|) = |p|^r` (`r = n/q`: the real `q`-th root, radcan's
   `rootR`), `exp (u + v) = exp u exp v`, `exp (n u) = exp u ^ n`.

### 2.3 Zero test

All `exp`/`ln` terms are now letters (`E_b`, `ln |p_i|`, `exp (1/d)`,
`ln (prime)`): `radcan_lra` (or `radcan_trig` if trig occurs). Conditions
left by radcan and by 2.1–2.2 are closed when easy (positivity of `exp`
letters, numerals, hypotheses, `lra`/`nra`) and otherwise given back.

---------------------------------------------------------------------------

## 3. What it guarantees

* Sound: every rewrite is an equality proved in Rocq (`field`, Stdlib
  lemmas, radcan). The searches (factoring, Gaussian elimination) are
  unproved and only produce candidates.
* Complete, for goals whose `exp`/`ln` arguments are rational functions of
  the variables and of lower letters (no roots inside arguments), up to:
  relations between constants (outside the theorem), the limits of the final
  radcan call (e.g. the `(1+x)/x` gap of `radcan`), and conditions that are
  true but not closed automatically.
* Not covered: roots inside `exp`/`ln` arguments beyond treating them as
  atoms (the "algebraic cases" TR223 excludes); ℂ; inequalities.

---------------------------------------------------------------------------

## 4. Work split

* G1 — exponential side (2.2): reification to rational functions, the ℚ
  Gaussian elimination, letters `exp (A_b / d_b)`, checked rewrites.
  File `explog/ExpLogG.v` (exp part), tests `explog/ExpLogGExpTests.v`.
* G2 — logarithm side (2.1): `ln |·|` form, factoring (reuse `ExpLogLn.v`'s
  reification), sign normalisation, conditions `p ≠ 0`.
  File `explog/ExpLogGLn.v`, tests `explog/ExpLogGLnTests.v`.
* Integration (me): unfolding, levels innermost first, the final call,
  condition closing; all prototype test files must pass or the failure is
  explained by section 3.

Tests: the goals of `ExpLogTests0.v`, `ExpLog{Exp,Ln,Hyp}Tests.v`,
`ExpLogTrigTests.v` — as tests only. Required specifically (generic cases a
heuristic misses): relations among ≥ 4 arguments, e.g.
`exp (x/2) * exp (x/3) * exp (x/6) = exp x`,
`exp (x/(x+1)) * exp (1/(x+1)) = exp 1`,
`exp (a/(a+b)) * exp (b/(a+b)) * exp (1/(x-1) - x/(x-1)) = 1`;
`ln (x^2) = 2 * ln (Rabs x)` under `x <> 0`.
