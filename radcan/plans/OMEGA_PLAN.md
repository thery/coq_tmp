# Roots of unity on ℂ: index law and cyclotomic relations (plan)

Status: a plan only. Nothing here is implemented. Written 2026-10-15 from the
sources of mathcomp 2.5 (`algebra/num_theory/numfield.v`,
`field/cyclotomic.v`, `field/algC.v`, `algebra/poly.v`,
`solvable/cyclic.v`) and of RADCAN (`PosRoot.v`, `RootC.v`, `NegRootC.v`,
`Cond.v`, `paper/Paper.v`, TUTORIAL parts 12 and 16).

Notation: `ω_n := n.-root (-1 : C)` on a `numClosedFieldType C`. This is
`wroot (rootC_negroot C) n`. Below we show that `ω_n = e^{iπ/n}`, so `ω_n` is
the primitive **2n**-th root of unity `ζ_{2n}`. Throughout, "U" means the
closed upper half plane (`0 <= 'Im z`).

---------------------------------------------------------------------------

## 0. Summary

* mathcomp defines `n.-root x` as the n-th root with the smallest argument in
  `[0, 2π)`. So `ω_n = e^{iπ/n}`. The header of `algC.v` says that
  "n.-root (-1) is a primitive 2nth root of unity … (this will be shown in
  file cyclotomic.v)". **This is not proved anywhere in mathcomp 2.5.**
  `cyclotomic.v` does not mention `nthroot` at all. The only facts available
  are `rootC_Re_max` (maximal real part) and `Im_rootC_ge0` (n > 1).
* The index law `ω_{nk} ^+ k = ω_n` and primitivity can both be proved from
  those two facts with trig-free arguments. Everything reduces to one
  inequality about two points of the unit upper half-circle (T1 below) plus
  some finite combinatorics on the powers of a root of unity. Estimate:
  400–600 lines in a new file, 2–4 agent-days. This is the only hard part.
* The case k = 2 is easy: `(2n).-root (-1) = sqrtC (n.-root (-1))`. The probe
  `sqrtC_char` below was checked.
* Quick win, independent of the hard part: when 2N divides 24
  (N ∈ {1,2,3,4,6,12}), `ω_N` has an explicit value in `Q(i, √2, √3)`:
  `ω_3 = (1 + √3 ω_2)/2`, `ω_4 = √2/2 (1 + ω_2)`, `ω_6 = (√3 + ω_2)/2`,
  `ω_12 = ((√6+√2) + (√6−√2) ω_2)/4`. Each value takes about 20 lines to
  prove. If `radcan` rewrites these `ω`s to the explicit values, the goals
  `ω_3² − ω_3 + 1 = 0`, `ω_4² = ω_2`, `ω_4 + ω_4⁻¹ = √2` and the paper's (2)
  (second reading) all become provable with the existing machinery
  (`ω_2` reduced by `ω_2² = −1`, plus the real radicals).
* Cyclotomic reduction (B) does not need mathcomp's `'Phi_n`, which is not
  computable: it is defined by `Num.floor` over `algC`. A certificate is
  enough: the normaliser computes `p` (meant to be Φ_{2N}) and cofactors
  `h`, `g` over Z, checks `p·h = X^{2N} − 1` and
  `h·g = ∏_{q prime | 2N} (X^{2N/q} − 1)`, and a proved lemma gives
  `p(ω_N) = 0` from the primitivity of `ω_N`. Whether `p` really is Φ only
  affects completeness, not soundness.
* Index check on the task text: with `ω_n = n.-root(-1) = e^{iπ/n}`, the
  relation is **`ω_4 + ω_4⁻¹ = √2`** (`ω_4 = ζ_8`). `ω_8 + ω_8⁻¹ = √(2+√2)`
  is a nested radical. Paper (2): `ω_4⁻¹ − ω_4⁻³ − √2 = −ω_4³ + ω_4 − √2 = 0`
  uses the same relation (`ω_4 − ω_4³ = √2`).

---------------------------------------------------------------------------

## 1. How `n.-root` is defined in mathcomp 2.5 (`numfield.v`, l. 626–666)

```coq
Let Re2 z := z + z^*.
Definition nnegIm z := (0 <= 'i * (z^* - z)).            (* 0 <= 'Im z *)
Definition argCle y z := nnegIm z ==> nnegIm y && (Re2 z <= Re2 y).
Variant rootC_spec n (x : C) : Type :=
  RootCspec (y : C) of if (n > 0)%N then y ^+ n = x else y = 0
                     & forall z, (n > 0)%N -> z ^+ n = x -> argCle y z.
Fact rootC_subproof n x : rootC_spec n x.   (* sort argCle of the roots, take r`_0 *)
Definition nthroot n x := let: RootCspec y _ _ := rootC_subproof n x in y.
```

`n.-root x` is the first root, for the total preorder `argCle`, among the
roots of `'X^n - x` (from `closed_field_poly_normal`). If some root lies in
U, it is the root in U with the largest real part. For n > 1 there always is
one. So it is the root with the smallest argument in `[0, 2π)`, and for
`x = r e^{iθ}` with `θ ∈ [0, 2π)` we get `n.-root x = r^{1/n} e^{iθ/n}`.
Hence `ω_n = e^{iπ/n}`. Special cases: `0.-root x = 0`, `1.-root x = x`.

Lemmas available (all in `numfield.v`, section `ClosedFieldTheory`):

* Basic: `root0C`, `rootCK : (n>0) -> cancel n.-root (fun x => x ^+ n)`,
  `root1C`, `rootC0`, `rootC_inj`, `eqr_rootC`, `rootC_eq0`.
* Argument facts: `rootC_Re_max : (n>0) -> y ^+ n = x -> 0 <= 'Im y ->
  'Re y <= 'Re (n.-root x)` and `Im_rootC_ge0 : (n>1) -> 0 <= 'Im (n.-root x)`.
  These are the only exported consequences of `argCle`. `argCleP` and
  `neg_unity_root` are `Let`s, so they are local to the section.
* Order and sign: `rootC_lt0`, `rootC_ge0`, `rootC_gt0`, `rootC_le0`,
  `ler_rootCl`, `ler_rootC`, `ltr_rootCl`, `ltr_rootC`, `rootC_eq1`,
  `rootC_ge1`, `rootC_gt1`, `rootC_le1`, `rootC_lt1`.
* Algebra on nonnegatives: `exprCK`, `norm_rootC : |n.-root x| = n.-root |x|`,
  `rootCX`, `rootCpX`, `rootC1`, `rootCV`, `rootCMl`/`rootCMr`
  (`0 <= x -> n.-root (x*z) = n.-root x * n.-root z`), and `imaginaryCE :
  'i = sqrtC (-1)`, so **`ω_2 = 'i`**.
* Rectangular tools useful for the new proofs: `eqC_semipolar`
  (`|x|=|y| -> Re x = Re y -> 0 <= Im x * Im y -> x = y`), `normC2_Re_Im`,
  `ImM`, `Re_div`, `Im_div`, `Re_conj`, `Im_conj`, `Crect`, `conjCK`.
* Nothing about roots of unity, the index law, `(nk).-root = n.-root ∘
  k.-root`, or the primitivity of `ω_n`. `cyclotomic.v` has no lemma about
  `nthroot`, so the remark in `algC.v` is stale.

Roots of unity in mathcomp (`poly.v`, `cyclic.v`, `cyclotomic.v`):
`n.-unity_root`, `n.-primitive_root` (`primitive_root_of_unity`),
`prim_order_dvd`, `prim_expr_order`, `eq_prim_root_expr`, `exp_prim_root`,
`dvdn_prim_root`, `prim_root_exp_coprime`, `prim_rootP` (every n-th root of
unity is a power), `factor_Xn_sub_1`, `max_unity_roots`, `mem_unity_roots`,
`has_prim_root` (cyclic.v: in a field, n distinct n-th roots of unity contain
a primitive one), `separable_Xn_sub_1` (cyclotomic.v). Cyclotomic
polynomials: `cyclotomic z n` (any ring, defined from a primitive root z),
`root_cyclotomic : n.-primitive_root z -> root (cyclotomic z n) x =
n.-primitive_root x`, `prod_cyclotomic`, `'Phi_n : {poly int}`
(`Cyclotomic`, defined with `C_prim_root_exists` on **algC** and
`Num.floor`, so not computable), `Cintr_Cyclotomic` (algC only),
`prod_Cyclotomic : \prod_(d <- divisors n) 'Phi_d = 'X^n - 1` (over int, so
it maps to any ring), `size_Cyclotomic`, `Cyclotomic_monic`,
`minCpoly_cyclotomic` (algC).

---------------------------------------------------------------------------

## 2. Can `(nk).-root (-1) ^+ k = n.-root (-1)` be proved? Yes. Route and size.

### 2.1 The easy case k = 2 (checked)

```coq
Lemma sqrtC_char (C : numClosedFieldType) (w y : C) :
  y ^+ 2 = w -> 0 < 'Im y -> sqrtC w = y.
Proof.
move=> yw Iy; have := rootCK (isT : (0 < 2)%N) w; rewrite -yw => /eqP.
rewrite eqf_sqr => /orP[/eqP //|/eqP sN].
have := @Im_rootC_ge0 _ 2 (y ^+ 2) isT; rewrite sN raddfN /= oppr_ge0.
by rewrite real_leNgt ?Iy.
Qed.
```

(Checked with the rocq-radcan-agent server, in an mathcomp-only preamble.)
For n ≥ 2, `ω_n` is in U, and `(2n).-root (-1) = sqrtC ω_n`. Here is why.
If v is a root of `X^{2n}+1` in U, then either `v²` is in U, and then
`Re v² ≤ Re ω_n` by maximality; since `Re v² = 2 (Re v)² − 1` this gives
`Re v ≤ Re (sqrtC ω_n)`, because both have nonnegative real part. Or `v²` is
not in U, and then `Re v ≤ 0 ≤ Re (sqrtC ω_n)`. So `ω_{2^a n} ^+ 2^a = ω_n`
is about 60 lines. The odd case needs the general argument.

### 2.2 General case: an elementary "arc" theory (new file `UnitArc.v`)

Let U1 be the set of points of the unit circle in U. The general argument
rests on one inequality:

**(T1)** For p, q in U1: `'Re q <= 'Re p -> 0 <= 'Im (q * p^*)` and
`0 < 'Im (q * p^*) -> 'Re q < 'Re p`. (The converse of the first fails only
for p = −1, q = 1.) Write p = a + ib and q = c + id with b, d ≥ 0 and
a² + b² = c² + d² = r. The proof is the identity

  (a d − c b)(b + d) = (a − c)(r + a c + b d) + a((c²+d²) − (a²+b²)),

together with `r + ac + bd ≥ 0` (Cauchy–Schwarz). It also needs the case
`b + d = 0`.

Two consequences of T1, each a few lines:

* (T2) "no wrap": if s, t are in U1 and `Re s + Re t >= 0`, then
  `0 <= Im (s t)`. This is T1 applied to p = s and q = −t^*.
* (T3) "rotation": if a, θ and aθ are in U1 and `0 < Im θ`, then
  `Re (aθ) < Re a`. This is T1 strict, because `(aθ) a^* = θ`.

Then come the combinatorics on the 2k-th roots of unity W (k ≥ 1). The list
of roots comes from `closed_field_poly_normal ('X^(2k) - 1)`. It has 2k
distinct elements by `separable_Xn_sub_1`, and W is closed under
multiplication, conjugation and negation.

1. Let θ be the element of `W ∩ U ∖ {1}` with the largest real part. It
   exists because the set is finite and −1 is in it. This is a small argmax
   lemma on a seq, about 20 lines.
2. While `θ^j ≠ −1`, θ stays in the sector: `θ^i` is in U for i ≤ j+1, and
   `Re θ^i` is strictly decreasing. Proof by induction. A wrap at step j+1
   (`Re θ^j + Re θ < 0`) would make `w := −(θ^j)^*` an element of
   `W ∩ U ∖ {1}` with `Re w = −Re θ^j > Re θ`, which contradicts the choice
   of θ (trivial). Otherwise use T2 and T3.
3. Let j0 be the first exponent with `θ^{j0} = −1`; it exists because W is
   finite and the `θ^i` are distinct while `Re` decreases. Then θ has order
   2j0, so `2j0 | 2k`. If `j0 < k`, pick w in W that is not a power of θ
   (counting), and replace it by its conjugate if needed so that w is in U.
   Find i < j0 with `Re θ^{i+1} < Re w < Re θ^i`; the strict inequalities
   come from `eqC_semipolar`. By T1, `v := w (θ^i)^*` is in `W ∩ U ∖ {1}`
   and `Re v > Re θ`, a contradiction. So j0 = k: θ is a **primitive 2k-th
   root of unity**, `θ^k = −1`, and `Re θ^i` is strictly decreasing on
   `[0, k]` with `θ^i` in U.
4. `θ = ω_k`. θ is a root of `X^k+1` in U, so `Re θ ≤ Re ω_k`
   (`rootC_Re_max`). `ω_k` is in `W ∩ U ∖ {1}`, so `Re ω_k ≤ Re θ`. Both
   are in U1, so `eqC_semipolar` gives equality. **Theorem `omega_prim`:**
   `(2k).-primitive_root (k.-root (-1))`, plus the sector facts.
5. **Index law** `omega_exp : ω_{nk} ^+ k = ω_n` (n, k > 0). Let θ = ω_{nk}
   and z = θ^k. Then z^n = −1 and z is in U (k ≤ nk). Take any root u of
   `X^n+1` in U. It is `θ^i` with i < 2nk (`prim_rootP`). If i > nk, then
   `Im u = −Im θ^{i−nk} ≤ 0`, so u = −1. Otherwise `θ^{in} = −1` forces
   `i ≡ k (mod 2k)`, so i ≥ k and `Re u ≤ Re z` (monotonicity on `[0, nk]`).
   So z is the max-Re root in U, and `eqC_semipolar` with `rootC_Re_max`
   gives z = ω_n. Generalisation, not needed here: the composition law
   `(n*k).-root x = n.-root (k.-root x)`.

Size and difficulty: T1 is 40–60 lines of real-closed sign reasoning. These
fields are numClosedField elements that are real, so the proofs need
`real_*` lemmas and there is no `nra`. Steps 1–5 take 250–400 lines. With
helper lemmas, 400–600 lines in all, **2–4 agent-days**. Risks:

* there is no `ring` tactic, because algebra-tactics is not installed. The
  identities can be proved by `radcan` itself: `arc_id` above is a pure
  polynomial identity, which the `MStd` normaliser decides. Otherwise they
  must be rewritten by hand.
* the finite combinatorics (argmax, counting, discrete IVT along
  `Re θ^i`) are where the work goes.
* This is self-contained mathcomp material and a good upstream candidate:
  the claim in the `algC.v` header is still unproved.

Other routes that were considered:

* Sector characterisation by `argCle` sorting: it needs the same monotonicity.
* Trigonometry: not available on an abstract `numClosedFieldType`.
* Going through algC and `'Phi`: `Cintr_Cyclotomic` is stated only for algC,
  and the problem is the choice of root, not the polynomial.
* `ω_n` is the max-Re root in U with only roots of `X^n+1` as competitors:
  the wrap argument needs the whole group W, because `−(θ^j)^*` is a root of
  `X^n+1` only when n + j is odd. So step 1 uses `W ∖ {1}`.

---------------------------------------------------------------------------

## 3. `ω_n` is a primitive (2n)-th root, and Φ_{2n}(ω_n) = 0

Primitivity is step 4 of §2.2. Its cost is included there, and it cannot be
proved more cheaply than the index law: the content is the same.

Getting Φ_{2n}(ω_n) = 0 from it:

* Using mathcomp: map `prod_Cyclotomic` with `map_poly intr` into C.
  z is a root of `X^m − 1`, so z is a root of some `intr 'Phi_d` with d | m.
  If d < m, then `'Phi_d | X^d − 1` (again by `prod_Cyclotomic`), so
  `z^d = 1`, which contradicts primitivity. This gives `root (map_poly intr
  'Phi_m) z` in any `numClosedFieldType`, in about 25 lines. But the
  normaliser cannot compute `'Phi_m`, so this only helps to state a theorem.
* **Recommended**: a certificate lemma that does not mention `'Phi`:

  ```
  Lemma prim_root_cert (F : idomainType) m (z : F) (p h g : {poly F}) D :
    m.-primitive_root z -> all (fun d => 0 < d < m)%N D ->
    p * h = 'X^m - 1 -> h * g = \prod_(d <- D) ('X^d - 1) -> root p z.
  ```

  The proof: `h.[z] * g.[z]` is not 0 because each `z^d − 1` is not 0, so
  `h.[z]` is not 0; and `p.[z] h.[z] = 0`. About 20 lines. The normaliser
  works on `seq Z`, with a Horner bridge to `map_poly intr` (or directly to
  `nf`). It computes Φ_m recursively by exact monic division,
  `Φ_m = (X^m−1) / ∏_{d|m,d<m} Φ_d`, takes `D = [m/q | q prime, q | m]`,
  computes `g` by division, and checks both products by boolean equality.

---------------------------------------------------------------------------

## 4. How the normaliser would use this

Current state (Cond.v): `omega_c = RCst (-1)`. `ARoot n omega_c` is `ω_n`.
It is created by `nf_rootE` in modes `MNeg`/`MNegW` as `omega_nf n`, reduced
only by `ω_n^n = −1` (`vextract`, with no sign condition: `ge0_cond`), and
inverted by `vsplit_omega`/`omega_inv`. `vmerge` skips `ω` atoms
(`neg_mode m && is_omega e`). `radcan_check` compares the normal forms of
the two sides separately. Soundness only uses the abstract `negroot` record
(`wroot`, `prootNw`, `wrootK`), which says nothing about indices.

New laws are needed as a **new record** next to `negroot`, so that the
generic soundness proofs can use them. It goes in a new file, so that the
shared `PosRoot.v` is not edited:

```coq
Record cycroot (F : numFieldType) (r : posroot F) (w : negroot r) : Prop := {
  wrootX    : forall n k, (0 < n)%N -> (0 < k)%N -> wroot w (n * k) ^+ k = wroot w n;
  wroot_prim: forall n, (0 < n)%N -> (2 * n).-primitive_root (wroot w n) }.
Record smallroot (F : numFieldType) (r : posroot F) (w : negroot r) : Prop := {
  wroot3 : wroot w 3 = (1 + proot r 2 3 * wroot w 2) / 2;
  wroot4 : wroot w 4 = proot r 2 2 / 2 * (1 + wroot w 2);
  wroot6 : wroot w 6 = (proot r 2 3 + wroot w 2) / 2;
  wroot12: wroot w 12 = (proot r 2 6 + proot r 2 2
                          + (proot r 2 6 - proot r 2 2) * wroot w 2) / 4 }.
```

These are split so that the cheap `smallroot` can ship first. Instances on
ℂ: `rootC_smallroot C` (§5, Ω1) and `rootC_cycroot C` (§2.2).

### (Q) Small cyclotomic fields: unfold `ω_N` when 2N | 24 (quick win)

In `nf_rootE`, in neg mode, when `n ∈ {3,4,6,12}`, produce the explicit
`nf` in place of `omega_nf n`, and re-simplify the product with the existing
`nf_simp` (`√2·√2 = 2`, `√2·√3` against `√6` by M5). The `ω_N` atoms that
are already in the input (`n.-root (-1)` written by the user) go through the
same path, because `RRootE n (RCst -1)` is normalised by `nf_rootE`.
Afterwards `ω_2` is the only root of unity left for these N. The normal form
is then canonical, because the real radicals of positive rationals stay
linearly independent over `Q(i)`: in Kneser's criterion, ζ_4 ∈ Q(i).

What it solves: `ω_3² − ω_3 + 1 = 0`, `ω_4² = ω_2`, `ω_6³ = ω_2`,
`ω_4 + ω_4⁻¹ = √2`, `ω_12 ^+ 2 = ω_6`, and paper (2), second reading,
under radcan's side condition. The two `Fail` goals of TUTORIAL Part 16
become provable.

### (A) Merging `ω` atoms across indices (needs `wrootX`)

Remove the `neg_mode && is_omega` exclusion in `vmerge` and let `ω` atoms
go through the same two rewrites as real roots, with no sign condition:

* `ω_n^{k1} ω_m^{k2} → ω_L^{k1 L/n + k2 L/m}` with `L = lcm n m`;
* `ω_n^k → ω_{n/g}^{k/g}` with `g = gcd k n > 1`.

Both follow from `wrootX`. Together with `ω_n^k → −ω_n^{k−n}` (already
there), every monomial carries at most one root of unity, written as
`±ω_n^k` with `0 ≤ k < n` and `gcd(k,n) = 1`. This form is unique (it is
`±e^{iπk/n}` with k/n in lowest terms). It does not see additive relations,
which are (B). The soundness lemma for the new `vmerge` case is a sibling of
the existing one, where the `proot` laws are replaced by `wrootX`/`wrootK`.

### (B) Reduction modulo Φ_{2N} (needs `wroot_prim`)

This is a post-pass on the two final normal forms (p1, p2) in
`radcan_check_neg`:

1. N = lcm of the `ω` indices in the monomials of p1 and p2. `ω` atoms
   hidden inside inverse or nested atoms are left alone: this is sound but
   incomplete.
2. Lift: `ω_n^k → ω_N^{kN/n}` (by `wrootX`). The exponents are then below N.
3. Reduce each exponent j ≥ d = φ(2N) with `ω^d = −Σ_{i<d} p_i ω^i`, where
   `p = Φ_{2N}` is monic and checked by the certificate of §3. A fuel of N
   rounds is enough.
4. Compare. The pass changes neither side's value; its soundness lemma is
   `nf_interp (cyc_pass N p) = nf_interp p`.

The result is canonical over the coefficient ring (variables and real
radicals) as long as `Q(ζ_{2N})` is linearly disjoint from the real
radicals. This fails exactly for square roots `√D` with `cond(D) | 2N`
(`cond(D) = D` if `D ≡ 1 mod 4`, else `4D`). Cube and higher roots of
positive rationals never lie in an abelian extension. Cost of the
Φ_m computation: φ(2N) ≤ 2N; for N up to about 60 vm_compute is
instantaneous.

### (C) Relations between `ω`s and real radicals: limited scope

General mechanism: `√D ∈ Q(ζ_{2N})` iff `cond(D) | 2N`, and `√D` is then a
Gauss sum in `ω_N`. Checking `G(ω)² = D` modulo Φ is easy and sound, but
that only gives `G(ω) = ±√D`. Fixing the **sign** needs inequalities on
`Re ω^j`, which is Gauss's sign problem in general. **Proposed scope:**

* (Q) above already covers everything for 2N | 24, with no Φ: √2, √3 and √6
  together with ω_2, ω_3, ω_4, ω_6 and ω_12.
* With (B), add a small table of eliminations, used only when an `ω` with
  `cond(D) | 2N` is present (an expression without `ω` keeps `√2` as it is):

  | D | condition | identity (ω = ω_N, after lifting) |
  |---|-----------|-----------------------------------|
  | 2 | 4 ∣ N  | √2 = ω_4 − ω_4³ |
  | 3 | 6 ∣ N  | √3 = ω_6 − ω_6⁵ |
  | 5 | 5 ∣ N  | √5 = 2ω_5 − 2ω_5⁴ − 1 |

  Monomials whose square-root part contains √2, √3 or √5 are rewritten
  factor by factor; the existing basis is made of primes, so √6 = √2·√3 is
  handled. Proofs: rows 2 and 3 follow from the explicit `ω_4` and `ω_6`.
  Row 5 is proved by squaring modulo Φ_10 (gives ±√5); the sign comes from
  `Re ω_5 ≥ 0`, which holds because ω_5² is in U (sector fact, or directly
  `Im ω² = 2 Re ω Im ω`).
* Known incompleteness that would be documented: √D for other D (√7 with
  28 | 2N, √21 with 21 | N, …), `ω` inside denominators or nested radicals,
  and nested values such as `ω_8 + ω_8⁻¹ = √(2+√2)`.

---------------------------------------------------------------------------

## 5. Milestones (easy to hard)

| # | content | files | effort | risk |
|---|---------|-------|--------|------|
| Ω0 | Characterisation lemmas: `sqrtC_char` (done in a probe); `rootC_char` (`u^n=x`, u in U, max Re among roots in U ⇒ `u = n.-root x`, via `eqC_semipolar` and `rootC_Re_max`); `ω_1 = −1`, `ω_2 = 'i`. | new `OmegaC.v` | ½ day | low |
| Ω1 | Explicit `ω_3` (factor `X³+1 = (X+1)(X²−X+1)`), then `ω_6 = sqrtC ω_3`, `ω_4 = sqrtC 'i`, `ω_12 = sqrtC ω_6` with `sqrtC_char`. The squares and cubes are radcan-provable once the build is stable. Record `smallroot` and instance `rootC_smallroot C`. | `OmegaC.v` (+ record in a new `OmegaRoot.v`) | ½–1 day | low |
| Ω2 | Mode (Q): in `nf_rootE` (neg mode, n ∈ {3,4,6,12}) emit the explicit nf, then simp; soundness through `smallroot`; new checker theorem `radcan_eq_refined_small`; `radcan` dispatch on `n.-root` goals over C. Turn the Part 16 `Fail`s and paper (2) (second reading) into proofs. | `Cond.v`, `NegRootC.v`, `Tactic.v`, `Examples.v`, `paper/Paper.v`, TUTORIAL Part 16, README | 1–2 days | medium: interaction with `MNegW`/`flip_odd` and `omega_inv`; canonicity relies on M5 for √2·√3 |
| Ω3 | `UnitArc.v`: T1–T3, argmax, sector induction, `omega_prim`, `omega_exp` (index law), and `(2n).-root(-1) = sqrtC ω_n`; record `cycroot` with instance `rootC_cycroot C`. | new `UnitArc.v`, `OmegaC.v` | 2–4 days | **high**: no `ring`/`nra`, finite combinatorics; a mathcomp upstream candidate |
| Ω4 | (A): `ω` merging in `vmerge` (lcm and gcd rules) with `wrootX`; soundness sibling lemmas. Examples: `ω_4² = ω_2`, `ω_8⁴ = ω_2`, `ω_6 ω_3 = ω_2`… | `Cond.v`, `NegRootC.v` | 1–2 days | medium: termination and fuel of `vmerge` unchanged; check `MNegW` |
| Ω5 | (B): Φ computation on `seq Z`, certificate lemma `prim_root_cert`, Horner bridge, post-pass (lift to `ω_N`, reduce mod Φ_{2N}) in `radcan_check_neg`. Examples: `ω_5⁴ − ω_5³ + ω_5² − ω_5 + 1 = 0`, `ω_9 ^+ 6 − ω_9 ^+ 3 + 1 = 0`. | new `Cyclo.v`, `Cond.v`, `NegRootC.v` | 2–3 days | medium: nf plumbing; global N across both sides |
| Ω6 | (C) table √2/√3/√5 with (B), only when a matching `ω` is present. | `Cyclo.v`, `Cond.v` | 1–2 days | medium: the sign proof for √5; keeping the form canonical with the M5 basis |
| Ω7 (optional) | General composition law `(n*k).-root x = n.-root (k.-root x)` from the sector theory; upstream PR to mathcomp (`algC.v` header claim). | `UnitArc.v` | 1–2 days | medium |

Recommended order: Ω0 → Ω1 → Ω2 (the paper and TUTORIAL gains, without the
hard math), then Ω3 → Ω4 → Ω5 → Ω6. Ω3 is on the critical path for (A) and
(B) only.

Files touched (later, by the implementing agents): new `OmegaRoot.v`
(records), `OmegaC.v`, `UnitArc.v`, `Cyclo.v`; `Cond.v`, `NegRootC.v`,
`Tactic.v`, `_CoqProject`, `Examples.v`, `paper/Paper.v`, `TUTORIAL.md`
(Part 16 and the "What does not work yet" section), and `README.md`.
`PosRoot.v` does not need to change if the records live in `OmegaRoot.v`.
Putting them next to `negroot` would be a change to the shared file, to be
agreed with its owner.

Notes:
* The record fields hold only for the principal roots of ℂ. Abstract
  `negroot`s keep the current behaviour, so the new modes need a
  `cycroot`/`smallroot` in context, or the `rootC_*` instances, exactly as
  `negroot` is found today.
* During this study the shared build was being rebuilt (`Radcan.vo makes
  inconsistent assumptions over Radcan.Poly`), so the radcan-based probes
  (`omega3E`, `omega4E`, `omega12E`, `arc_id`) were written but could not be
  run. They should be rerun once the build is stable.
