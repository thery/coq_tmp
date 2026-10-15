# Draft PR for math-comp: `n.-root (-1)` is a primitive 2n-th root of unity

Status: draft only, not opened (the user opens PRs himself).
Code: `plans/mathcomp/nthroot_unity.v` (721 lines, standalone, mathcomp only,
compiles against mathcomp 2.5 / Rocq 9.1.1, no axioms: `Print Assumptions`
closed for the four main lemmas).

## Title

Prove that `n.-root (-1)` is a primitive `2n`-th root of unity, and that
principal roots compose: `(n * k).-root x = n.-root (k.-root x)`

## Description

The header of `algC.v` says:

> Note that n.-root (-1) is a primitive 2nth root of unity, an thus not equal
> to -1 for n odd > 1 (this will be shown in file cyclotomic.v).

This has never been proved: `cyclotomic.v` does not mention `nthroot`. This
PR proves it, for any `C : numClosedFieldType`, together with the
composition law of principal roots, which holds for every `x` (no hypothesis
on the argument of `x`).

New lemmas (section variable `C : numClosedFieldType`):

```coq
Lemma eq_rootC_Re_max n x y : (0 < n)%N -> y ^+ n = x -> 0 <= 'Im y ->
  (forall z, z ^+ n = x -> 0 <= 'Im z -> 'Re z <= 'Re y) -> n.-root x = y.
Lemma rootCN1_prim n : (0 < n)%N -> (2 * n).-primitive_root (n.-root (-1 : C)).
Lemma rootCN1_Re_max n w : (0 < n)%N -> w ^+ (2 * n) = 1 -> 0 <= 'Im w ->
  w != 1 -> 'Re w <= 'Re (n.-root (-1 : C)).
Lemma Im_rootCN1_ge0 n : 0 <= 'Im (n.-root (-1 : C)).
Lemma Im_rootCN1_gt0 n : (1 < n)%N -> 0 < 'Im (n.-root (-1 : C)).
Lemma rootCN1_index n k : (0 < n)%N -> (0 < k)%N ->
  (n * k).-root (-1 : C) ^+ k = n.-root (-1).
Lemma exp_rootC_mul n k (x : C) : (0 < n)%N -> (n * k).-root x ^+ n = k.-root x.
Lemma rootC_mul n k (x : C) : (n * k).-root x = n.-root (k.-root x).
```

The proofs avoid trigonometry (there is none on a `numClosedFieldType`).
Their only tools are `rootC_Re_max`, `Im_rootC_ge0` and `eqC_semipolar`, plus
an elementary "calculus of arguments" on the closed upper half of the unit
circle, where u comes before v when `'Re v <= 'Re u`:

* `arc_Im`: for `|p| = |q|`, p and q in `0 <= 'Im`, `'Re q <= 'Re p`
  implies `0 <= 'Im (q * p^*)` (sign case analysis on the coordinates), and
  its converse `arc_conv` (except for `q = - p`), plus "no wrap" lemmas for
  products (`arc_T2`, `arc_wrap`) and the monotonicity of products
  (`arc_add`).
* Primitivity: take `t`, the 2n-th root of unity `w != 1` in `0 <= 'Im` with
  the largest real part (`unity_argmax`; the roots come from
  `closed_field_poly_normal`). Dividing a root of unity in the upper half
  plane by `t` keeps it in the upper half plane and strictly increases its
  real part (`descent_step`), so every such root is a power of `t`
  (`unity_descent`). Applied to a primitive 2n-th root (in `0 <= 'Im` after
  conjugation if needed), this makes `t` primitive, so `t ^+ n = -1`, and
  `eq_rootC_Re_max` gives `t = n.-root (-1)`.
* Index law: same descent, using `rootC_Re_max` on `n.-root (-1)`.
* Composition: for `r = (n * k).-root x` (x != 0), `r / |r|` lies strictly
  before `ω^2` with `ω = (n * k).-root (-1)` (`rootC_arc`); the powers
  `(r / |r|) ^+ j`, `j <= n`, stay strictly before `ω ^+ 2j` (`arc_add` and
  the sector property of `ω`); with `rootCN1_sqr_Re_max` this gives
  `r ^+ n = k.-root x` (`exp_rootC_mul`), and then `rootC_mul` via
  `eq_rootC_Re_max`.

Helper lemmas are `Local`. The file also contains `prim_root_existsC`
(existence of a primitive m-th root of unity in any `numClosedFieldType`);
`C_prim_root_exists` in `cyclotomic.v` is the same statement for `algC`
only, so it could be generalised instead.

## Where to put it

Two options for the maintainers:

1. Append the section to `field/cyclotomic.v` (the file named in the
   `algC.v` header; it already imports `cyclic` and `separable`) and fix the
   header of `algC.v` to point to the lemma names (and the typo "an thus").
2. A new file `field/nthroot.v` (or `algebra/num_theory/`, but
   `has_prim_root` lives in `solvable/cyclic.v`).

Proposed header change in `algC.v`:

```
(*               Note that n.-root (-1) is a primitive 2nth root of unity,    *)
(*               and thus not equal to -1 for n odd > 1 (see rootCN1_prim in  *)
(*               cyclotomic.v).                                               *)
```

## Checklist before opening

* rename to taste (`rootCN1_prim`, `rootCN1_index`, `rootC_mul`,
  `exp_rootC_mul`, `eq_rootC_Re_max` are proposals);
* make `C` implicit in `rootCN1_prim`, `rootCN1_index`, `Im_rootCN1_*`
  (`Arguments ... {C}`) if the maintainers prefer;
* CHANGELOG_UNRELEASED entry ("added lemmas `rootCN1_prim`, ...").
