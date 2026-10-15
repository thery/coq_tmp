# RADCAN in Rocq — tutorial

This tutorial grows with the project. Each part explains one layer of the
development and shows how to use it with a small Rocq script. Every script
in this file compiles against the current files in `rocq/`.

To run them, put the script in a file next to the project and compile with
the project's load path:

```sh
cd ~/claudeExp/radcan/rocq
eval "$(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=native --set-switch)"
rocq compile -w -notation-overridden,-ambiguous-paths -R . Radcan MyTest.v
```

All scripts start with the same header:

```coq
From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts RootC RootR Syntax.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
```

## What we are building

The aim is a tactic that proves equalities between expressions built from
integers, `+`, `-`, `*`, powers and n-th roots of positive integers, such as

    √2 · √3 = √6        (1 + √2)² = 3 + 2√2        √12 − √3 = √3

The tactic works by *reflection*:

1. it reads the goal and builds a syntax tree for each side (*reification*);
2. a function written in Rocq computes a normal form for each tree, using only
   integer arithmetic, which `vm_compute` runs fast;
3. it then applies a proved lemma: if the two normal forms are equal, the two
   expressions are equal.

The same tactic must work on real numbers (any `rcfType`) and on complex
numbers (any `numClosedFieldType`). So all the work is done once, over an
abstract field equipped with a root function.

## Part 1 — the root interface (`PosRoot.v`, `PosRootFacts.v`)

`PosRoot.v` defines a record `posroot F` for a field `F : numFieldType`.
It contains a function `proot n a`, meant to be "the nonnegative n-th root
of `a`", and three properties. Each property only holds for `0 < n` and
`0 <= a`:

| field       | statement                                   |
|-------------|---------------------------------------------|
| `proot_ge0` | `0 <= proot n a`                            |
| `prootK`    | `proot n a ^+ n = a`                        |
| `prootM`    | `proot n (a * b) = proot n a * proot n b`   |

The restriction to `0 <= a` is essential. Without it we could derive
`1 = √1 = √((-1)(-1)) = √(-1)·√(-1) = -1`.

Everything else is proved only from these three fields. `PosRootFacts.v`
collects the derived lemmas. `proot_eq` gives uniqueness: a nonnegative `x`
with `x ^+ n = a` is the root. `proot_mulr` changes the index:
`proot n a = proot (n*k) (a^+k)`. The file also has `prootX`, `prootXK`,
`prootMn`, `proot_1`, `proot_0`, `proot1n`, `prootM_big`, `proot_gt0`,
`proot_proot`, `proot_inj` and `prootV`.

Here are some small proofs by hand, for an arbitrary field with roots:

```coq
Section Tutorial1.
Variables (F : numFieldType) (r : posroot F).

(* √2 squared is 2: the side conditions 0 < 2, 0 <= 2 are closed by // *)
Lemma sqrt2_sq : proot r 2 2 ^+ 2 = 2.
Proof. by rewrite prootK. Qed.

Lemma sqrt2_ge0 : 0 <= proot r 2 2.
Proof. by apply: proot_ge0. Qed.

(* √2·√3 = √6: product of roots, then 2*3 = 6 on numerals *)
Lemma sqrt2_sqrt3 : proot r 2 2 * proot r 2 3 = proot r 2 6.
Proof. by rewrite -prootM // -natrM. Qed.

(* √4 = 2, by uniqueness *)
Lemma sqrt4 : proot r 2 4 = 2.
Proof. by apply: proot_eq => //; rewrite expr2 -natrM. Qed.

(* ∛2 = ⁶√4: change of index *)
Lemma cbrt_sqrt : proot r 3 2 = proot r 6 4.
Proof. by rewrite (proot_mulr r (k := 2)) // expr2 -natrM. Qed.
End Tutorial1.
```

Even these tiny facts already need a few rewrites, and the side conditions
and numeral arithmetic make them tedious. The tactic is meant to automate
this work.

## Part 2 — real and complex instances (`RootR.v`, `RootC.v`)

A generic lemma is used on a concrete field by supplying an instance of
`posroot`:

- `RootC.v`: `rootC_posroot : posroot C` for any `C : numClosedFieldType`
  (for example the algebraic numbers). It is built on mathcomp's `n.-root`, and
  `rootC_posrootE : proot rootC_posroot n a = n.-root a` connects the two.
- `RootR.v`: `rootR_posroot R : posroot R` for any `R : rcfType`. mathcomp
  has no real n-th root, so `rootR n a` is defined from the intermediate
  value theorem (`poly_ivt`). It is not computable, which does not matter
  here because the tactic never evaluates roots in `R`.

Here the generic lemma `sqrt2_sqrt3` from Part 1 is used on both fields:

```coq
Section Tutorial2.
Variables (R : rcfType) (C : numClosedFieldType).

Lemma sqrt2_sqrt3_R :
  proot (rootR_posroot R) 2 2 * proot (rootR_posroot R) 2 3
  = proot (rootR_posroot R) 2 6 :> R.
Proof. exact: sqrt2_sqrt3. Qed.

(* on C the goal can be stated with mathcomp's own n.-root *)
Lemma sqrt2_sqrt3_C : 2.-root 2 * 2.-root 3 = 2.-root 6 :> C.
Proof. by rewrite -!rootC_posrootE sqrt2_sqrt3. Qed.
End Tutorial2.
```

## Part 3 — the syntax (`Syntax.v`)

Reflection needs the expressions as data. `Syntax.v` defines

```coq
Inductive rexpr : Type :=
  | RCst  : Z -> rexpr                     (* integer constant  *)
  | RRoot : positive -> positive -> rexpr  (* RRoot n p = proot n p *)
  | RAdd  : rexpr -> rexpr -> rexpr
  | ROpp  : rexpr -> rexpr
  | RSub  : rexpr -> rexpr -> rexpr
  | RMul  : rexpr -> rexpr -> rexpr
  | RPow  : rexpr -> nat -> rexpr
  | RVar  : nat -> rexpr                   (* variables, Part 7 *)
  | RInv  : rexpr -> rexpr                 (* e^-1, Part 8 *)
  | RRootE : positive -> rexpr -> rexpr.   (* root of any expression, Part 9 *)
```

and `rinterp r env e : F`, the value of `e` in the field. (Since Part 9,
`rinterp r` is a notation for `rinterp_gen (proot r)`, and `rinterp0` reads
root-free terms without any root structure.) There is also a
constructor `RVar : nat -> rexpr` for variables (Part 7): `RVar i` means the
`i`-th element of the list `env : seq F`. With no variables, `env` is `[::]`. Indices and radicands
are `positive`, so every `RRoot n p` is a root of a positive number with a
positive index, and the side conditions of Part 1 always hold.

The interpretation computes back to the usual mathcomp expression. As a
result, the two sides below are equal by conversion (`by []`):

```coq
Section Tutorial3.
Variables (F : numFieldType) (r : posroot F).

Definition e1 : rexpr := RMul (RRoot 2%positive 2%positive) (RRoot 2%positive 3%positive).

Lemma e1_val : rinterp r [::] e1 = proot r 2 2 * proot r 2 3.
Proof. by []. Qed.

Lemma e2_val :
  rinterp r [::] (RPow (RAdd (RCst (Zpos 1)) (RRoot 2%positive 2%positive)) 2)
  = (1 + proot r 2 2) ^+ 2.
Proof. by []. Qed.
End Tutorial3.
```

(`%Z` is taken by mathcomp's `int`, which is why `Zpos 1` is written
instead of `1%Z`.)

The reification tactic does the reverse: it reads `proot r 2 2 * proot r 2 3`
and produces `e1`.

## Part 4 — reification (`Tactic.v`)

`radcan_reify r` turns a goal `a = b` into `rinterp r env ea = rinterp r env eb`.
It reads `+`, `-` (opposite and subtraction), `*`, `^+`, `0`, `1` and the
numerals `k%:R`. It also reads roots with a numeral index, written in any of three ways: `proot r n k`, mathcomp's `n.-root k`
(on ℂ), and `rootR n k` (on ℝ). A root of a positive numeral becomes `RRoot n p`, and a root of any
other expression becomes `RRootE n e` (Part 9). Any other subterm becomes a
variable (Part 7). The change is checked by conversion, so a mistake in the tactic
cannot produce a wrong goal.

`radcan_find_root` finds the root structure from the roots occurring in the
goal: `r` for `proot r`, `rootC_posroot C` for `n.-root`, and
`rootR_posroot R` for `rootR`.

```coq
Goal forall (F : numFieldType) (r : posroot F),
  (1 + proot r 2 2) ^+ 2 - 3 = 2 * proot r 2 2.
Proof. move=> F r. let r := radcan_find_root in radcan_reify r. Show. Abort.
(* rinterp r (RAdd (RPow (RAdd (RCst 1) (RRoot 2 2)) 2) (ROpp (RCst 3)))
   = rinterp r (RMul (RCst 2) (RRoot 2 2))                               *)

Goal forall (C : numClosedFieldType), 2.-root 2 * 2.-root 3 = 2.-root (6 : C).
Proof. move=> C. let r := radcan_find_root in radcan_reify r. Show. Abort.

Goal forall (R : rcfType), rootR 2 2 * rootR 2 3 = rootR 2 (6 : R).
Proof. move=> R. let r := radcan_find_root in radcan_reify r. Show. Abort.
```

## Part 5 — the real numbers of Stdlib (`Rstruct.v`, `RootRstd.v`)

`Rstruct.v` is borrowed from mathcomp-analysis (`reals_stdlib/Rstruct.v`)
and cut after its `rcfType` instance. It makes Stdlib's `R` (from
`Reals`) a mathcomp real closed field, so `rootR_posroot R` applies to it.
Goals written with Stdlib notation still use different symbols: `Rplus`,
`pow`, the numerals `IZR (Zpos p)` and `sqrt`. `RootRstd.v` proves the
translation lemmas, for example `sqrtE : 0 <= a -> sqrt a = rootR 2 a` and
`IZR_posE : IZR (Zpos p) = (Pos.to_nat p)%:R`. Its tactic `radcan_Rstd`
rewrites with them, and after that the reification works:

```coq
From Stdlib Require Import Reals.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import Rstruct PosRoot RootC RootR Syntax Tactic RootRstd.
Open Scope R_scope.

Goal sqrt 2 * sqrt 3 = sqrt 6.
Proof. radcan_Rstd. let r := radcan_find_root in radcan_reify r. Show. Abort.

Goal (1 + sqrt 2) ^ 2 - 3 = 2 * sqrt 2.
Proof. radcan_Rstd. let r := radcan_find_root in radcan_reify r. Show. Abort.
```

## Part 6 — normal forms (`Radcan.v`) and the full tactic `radcan`

`Radcan.v` computes a normal form for an `rexpr`. A normal form is a sum of
terms `c · ∏ proot nᵢ bᵢ ^+ eᵢ`, where `c` is an integer, each `bᵢ` is a
prime, `0 < eᵢ < nᵢ` and `gcd(eᵢ, nᵢ) = 1`. For example `√8` gives `2·√2`
and `∛2·√2` gives `⁶√(2⁵)`. The radicands are factored by trial division,
and the factorisation is checked by multiplication. Everything runs on
`Z`/`positive` under `vm_compute`, and each test example takes a few
milliseconds. The two main results, for any `F : numFieldType` and
`r : posroot F`, are

```coq
Theorem norm_sound e : rinterp r e = nf_interp r (norm e).
Theorem radcan_eq e1 e2 : nf_eqb (norm e1) (norm e2) -> rinterp r e1 = rinterp r e2.
```

The tactic `radcan` (in `Tactic.v`) has three steps. It reifies the goal
(Part 4), applies `radcan_eq`, and runs `vm_compute`. If the normal forms
differ, it fails with "radcan: the normal forms differ". `radcan_with r`
does the same with an explicit root structure. On Stdlib reals, run
`radcan_Rstd` first (Part 5).

```coq
From Stdlib Require Import Reals.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import Rstruct PosRoot RootC RootR Syntax Radcan Tactic RootRstd.
Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Section Generic.
Variables (F : numFieldType) (r : posroot F).
Lemma g1 : proot r 2 2 * proot r 2 3 = proot r 2 6. Proof. radcan. Qed.
Lemma g2 : (1 + proot r 2 2) ^+ 2 = 3 + 2 * proot r 2 2. Proof. radcan. Qed.
Lemma g3 : proot r 2 8 = 2 * proot r 2 2. Proof. radcan. Qed.
Lemma g4 : proot r 3 2 * proot r 2 2 = proot r 6 32. Proof. radcan. Qed.
Lemma g5 : proot r 2 12 - proot r 2 3 = proot r 2 3. Proof. radcan. Qed.
End Generic.

(* complex: mathcomp's n.-root *)
Lemma c1 (C : numClosedFieldType) : (3.-root 2) * (2.-root 2) = 6.-root 32 :> C.
Proof. radcan. Qed.

(* real closed field: rootR *)
Lemma rc1 (R : rcfType) : (rootR 2 2 + rootR 2 3) ^+ 2 = 5 + 2 * rootR 2 (6 : R).
Proof. radcan. Qed.

(* Stdlib reals *)
Local Open Scope R_scope.
Lemma s1 : sqrt 2 * sqrt 3 = sqrt 6. Proof. radcan_Rstd. radcan. Qed.
Lemma s2 : (1 + sqrt 2) ^ 2 = 3 + 2 * sqrt 2. Proof. radcan_Rstd. radcan. Qed.
Lemma s3 : sqrt 12 - sqrt 3 = sqrt 3. Proof. radcan_Rstd. radcan. Qed.

(* a false equality is refused *)
Goal sqrt 2 + sqrt 3 = sqrt 5.
Proof. radcan_Rstd. Fail radcan. Abort.
```

## Part 7 — variables outside roots

Like `ring`, the tactic treats any subterm it does not recognise as an
*atom*. Examples are a plain `x`, `sin x`, a power with a symbolic exponent,
or `f x` for an unknown function `f`. Atoms are collected in a list
`env`, and atom number `i` becomes `RVar i`. Two atoms are the same only if
they are syntactically equal.

The normal form now multiplies three parts in each term: an integer
coefficient, a monomial in the variables (for example `x²y`), and a monomial
in the roots. So the tactic proves polynomial identities over radicals:

```coq
Local Open Scope ring_scope.
Section Generic.
Variables (F : numFieldType) (r : posroot F) (x y : F).
Lemma v1 : x * proot r 2 2 = proot r 2 2 * x. Proof. radcan. Qed.
Lemma v2 : x * proot r 2 2 + x * proot r 2 2 = 2 * x * proot r 2 2. Proof. radcan. Qed.
Lemma v3 : (x + proot r 2 2) ^+ 2 = x ^+ 2 + 2 * x * proot r 2 2 + 2. Proof. radcan. Qed.
Lemma v4 : (x - y * proot r 2 3) * (x + y * proot r 2 3) = x ^+ 2 - 3 * y ^+ 2.
Proof. radcan. Qed.
Lemma v5 : (x + proot r 3 2) ^+ 3
         = x ^+ 3 + 3 * x ^+ 2 * proot r 3 2 + 3 * x * proot r 3 4 + 2.
Proof. radcan. Qed.
(* any unrecognised subterm is an atom, e.g. sin x on R or f x here *)
Variable f : F -> F.
Lemma v6 : f x * proot r 2 8 = 2 * proot r 2 2 * f x.
Proof. radcan. Qed.
End Generic.

Local Open Scope R_scope.
Lemma s4 (x y : R) : (x - y * sqrt 3) * (x + y * sqrt 3) = x ^ 2 - 3 * y ^ 2.
Proof. radcan_Rstd. radcan. Qed.
Lemma s5 (x : R) : (x + sqrt 2) ^ 2 = x ^ 2 + 2 * sqrt 2 * x + 2.
Proof. radcan_Rstd. radcan. Qed.
Lemma s6 (x : R) : sin x * sqrt 8 = 2 * sqrt 2 * sin x.
Proof. radcan_Rstd. radcan. Qed.
```

Roots of expressions with variables, such as `√x · √x = x`, are handled in
Part 9 (with the side condition `0 <= x`).

## Part 8 — division (milestone M2)

The syntax has one more constructor, `RInv : rexpr -> rexpr`, for `e^-1`. In
mathcomp `a / b` is `a * b^-1`, so the tactic reads `/` as well. On Stdlib
`R`, `radcan_Rstd` also rewrites `Rinv` and `Rdiv`. Normal-form coefficients
are now rationals (Stdlib `Q`, kept reduced), so `√2/2` has coefficient `1/2`.

The inverse of a normal form `d` is computed like this:

1. If `d` contains no variables, a candidate `u` is found by linear algebra
   over `Q` on the finite basis of root monomials. This is the paper's
   "rationalising the denominator".
2. The candidate is **checked**: `d·u` must normalise to `1`. In a field this
   proves `u = d⁻¹`, so no condition `d ≠ 0` is needed. The candidate
   search itself never has to be proved correct.
3. Otherwise (variables in `d`, failed check, or too many roots) the inverse
   stays an opaque atom `(d)⁻¹`. The tactic proves less but never fails or
   assumes anything. Cancelling `x / x` needs `x ≠ 0`, so it is done in
   Part 9, which leaves that condition as a goal.

```coq
Local Open Scope ring_scope.
Section Generic.
Variables (F : numFieldType) (r : posroot F) (x : F).
Lemma d1 : 1 / proot r 2 2 = proot r 2 2 / 2. Proof. radcan. Qed.
Lemma d2 : 1 / (1 + proot r 2 2) = proot r 2 2 - 1. Proof. radcan. Qed.
Lemma d3 : (proot r 2 3 + proot r 2 2) / (proot r 2 3 - proot r 2 2) = 5 + 2 * proot r 2 6.
Proof. radcan. Qed.
Lemma d4 : 1 / proot r 3 2 = proot r 3 4 / 2. Proof. radcan. Qed.
Lemma d5 : 1 / (1 + proot r 2 2 + proot r 2 3) = (2 + proot r 2 2 - proot r 2 6) / 4.
Proof. radcan. Qed.
Lemma d6 : x / proot r 2 2 + x / proot r 2 2 = x * proot r 2 2. Proof. radcan. Qed.
Lemma d7 : (x + proot r 2 2) / 3 = x / 3 + proot r 2 2 / 3. Proof. radcan. Qed.
End Generic.

Lemma dc (C : numClosedFieldType) : 1 / (1 + 2.-root 2) = 2.-root 2 - 1 :> C.
Proof. radcan. Qed.

Local Open Scope R_scope.
Lemma sd1 : 1 / sqrt 2 = sqrt 2 / 2. Proof. radcan_Rstd. radcan. Qed.
Lemma sd2 : / (sqrt 3 - sqrt 2) = sqrt 3 + sqrt 2. Proof. radcan_Rstd. radcan. Qed.

(* a false goal is refused *)
Goal 1 / sqrt 2 = sqrt 2. Proof. radcan_Rstd. Fail radcan. Abort.

Print Assumptions d5.   (* Closed under the global context *)
Print Assumptions sd2.  (* only the axioms of Stdlib's R, plus Epsilon and
                           functional extensionality used by Rstruct.v *)
```

The normal form is computed in a few milliseconds per example. Inverting
`1/(∛2+√3+⁵√7)` needs a 30-dimensional basis and takes about 0.5 s.

## Part 9 — variables under roots and side conditions (milestone M3)

Now a root can contain variables: `√(x²−1)` is reified as `RRootE 2 e`.
Some simplifications are only true under a condition, like `√(x²) = x` for
`0 ≤ x`. The paper (§3) fixes such ambiguities by rules and works with `x`
as a formal symbol. Here `x` is a value, so each rule application is
recorded as a **condition**:

- `0 ≤ B` when the root of a product is split into roots of its factors
  (`√(B₁·B₂) = √B₁·√B₂`), or when `√(B²)` is turned into `B`;
- `D ≠ 0` when `D · D⁻¹` is cancelled to `1`.

The radicands are decomposed over a *basis* of polynomials common to the
whole goal. This is the paper's Collins-style basis, refined by exact
division: for example `x − 1` divides `x² − 1`, which gives `x + 1`. The
decomposition is checked by multiplication. The normaliser returns the
normal form together with the list of conditions. The soundness theorem is

```coq
Theorem radcan_eq_cond [F] (r : posroot F) env [e1 e2] cs :
  radcan_check e1 e2 = Some cs -> all_conds r env cs ->
  rinterp r env e1 = rinterp r env e2.
```

`radcan_raw` proves the equality and leaves the conditions as separate goals,
**raw**, in the form they were produced: `0 <= x + 1`, `0 <= x - 1`,
`x - 1 != 0`. Plain `radcan` refines them first (Part 10). Goals with no variables under roots, such as those of Parts 6–8,
still produce no condition.

Goals with no root at all (rational-function cancellation) need no root
structure: the tactic then uses `radcan_eq_cond0` and works in any
`numFieldType`.

On Stdlib reals, `radcan_Rstd_back` translates a remaining condition back to
Stdlib notation, so that `lra` or `nra` can close it. `sqrt a = rootR 2 a`
now holds for every `a`, because both are `0` on negative numbers.

```coq
From Stdlib Require Import Reals Lra.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import Rstruct PosRoot RootC RootR Syntax Radcan Tactic RootRstd.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Section Generic.
Variables (F : numFieldType) (r : posroot F) (x y : F).

Lemma c1 : 0 <= x -> proot r 2 (x ^+ 2) = x.
Proof. move=> x_ge0. radcan_raw. exact: x_ge0. Qed.

Lemma c2 : 0 <= x -> proot r 2 (4 * x) = 2 * proot r 2 x.
Proof. move=> x_ge0. radcan_raw. exact: x_ge0. Qed.

Lemma c3 : 0 <= x -> proot r 3 x * proot r 3 (x ^+ 2) = x.
Proof. move=> x_ge0. radcan_raw. exact: x_ge0. Qed.

Lemma c4 : 0 <= x -> 0 <= y -> proot r 2 (x * y) = proot r 2 x * proot r 2 y.
Proof. move=> x_ge0 y_ge0. radcan_raw. all: by []. Qed.
(* radcan leaves:  0 <= x   and   0 <= y *)

(* three raw conditions, all consequences of 1 < x *)
Lemma c5 : 1 < x ->
  proot r 2 (x ^+ 2 - 1) / proot r 2 (x - 1) = proot r 2 (x + 1).
Proof.
move=> x_gt1. radcan_raw.
(* radcan leaves:  0 <= x + 1,   0 <= x - 1,   x - 1 != 0 *)
- by rewrite addr_ge0 // ltW // (lt_trans ltr01 x_gt1).
- by rewrite subr_ge0 ltW.
- by rewrite subr_eq0 gt_eqF.
Qed.

(* no root at all: rational-function cancellation *)
Lemma c6 : x - 1 != 0 -> (x ^+ 2 - 1) / (x - 1) = x + 1.
Proof. move=> h. radcan_raw. exact: h. Qed.

Lemma c7 : x + 1 != 0 -> x - 1 != 0 -> (x ^+ 2 - 1) / (x + 1) / (x - 1) = 1.
Proof. move=> h1 h2. radcan_raw. all: by []. Qed.

Lemma c8 : x != 0 -> x / x = 1.
Proof. move=> h. radcan_raw. exact: h. Qed.

Lemma c9 : x != 0 -> (x * y + x) / x = y + 1.
Proof. move=> h. radcan_raw. exact: h. Qed.
End Generic.

(* on Stdlib reals: radcan_Rstd_back + lra close the conditions *)
Local Open Scope R_scope.
Lemma sc5 (x : R) : 1 < x -> sqrt (x ^ 2 - 1) / sqrt (x - 1) = sqrt (x + 1).
Proof. move=> x_gt1. radcan_Rstd. radcan_raw. all: radcan_Rstd_back; lra. Qed.

Lemma sc6 (x : R) : 0 <= x -> sqrt (x ^ 3) = x * sqrt x.
Proof. move=> x_ge0. radcan_Rstd. radcan_raw. all: radcan_Rstd_back; lra. Qed.

Lemma sc7 (x : R) : x <> 1 -> (x ^ 2 - 1) / (x - 1) = x + 1.
Proof. move=> h. radcan_Rstd. radcan_raw. radcan_Rstd_back. lra. Qed.
```

Every normal form in this part is computed in about 0.01 s.

## Part 10 — refined conditions (`Refine.v`, milestone M4)

`Refine.v` turns the raw list into a shorter one:

- duplicates and conditions that are true on constants (`0 <= 3`) disappear,
  also with roots of constants: `0 <= 3 - 2 * sqrt 2` is proved by rational
  bounds on `sqrt 2` (`SignCert.v`);
- `0 <= x^-1` is read as `0 <= x`; `0 <= sqrt x`, `0 <= x * y` and
  `1 <= x ^+ 2` are dropped when they follow from `0 <= x`, `0 <= y`,
  `1 <= x` (the checker knows that roots and inverses of nonnegative
  expressions are nonnegative, and multiplies two hypotheses);
- a condition affine in one variable becomes a bound: `0 <= x - 1` becomes
  `1 <= x`, and `x + 1 != 0` becomes `x != -1`;
- for each variable only the strongest bounds are kept, and `1 <= x` together
  with `x != 1` becomes `1 < x`;
- conditions with several variables or of higher degree are handled in Part 15.

The refined list is accepted only after a checker proves that it implies the
raw one. The theorem `refine_sound` (refined ⇒ raw) is all the tactic
needs. Only reasoning valid in any `numFieldType` is used, so the same
refinement works on ℂ (`0 <= x^2` is never dropped, since it is false for
`x = i`).

`radcan` now leaves the refined conditions, and `radcan_raw` the raw ones:

```coq
From Stdlib Require Import Reals Lra.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import Rstruct PosRoot RootC RootR Syntax Radcan Refine Tactic RootRstd.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Section Generic.
Variables (F : numFieldType) (r : posroot F) (x y : F).

(* raw: 0 <= x + 1, 0 <= x - 1, x - 1 != 0   refined: 1 < x *)
Lemma f1 : 1 < x ->
  proot r 2 (x ^+ 2 - 1) / proot r 2 (x - 1) = proot r 2 (x + 1).
Proof. move=> x_gt1. radcan. exact: x_gt1. Qed.

(* raw: x + 1 != 0, x - 1 != 0   refined: x != -1, x != 1 *)
Lemma f2 : x != -1 -> x != 1 -> (x ^+ 2 - 1) / (x + 1) / (x - 1) = 1.
Proof. move=> h1 h2. radcan. all: by []. Qed.

(* raw: 0 <= x + 1, 0 <= x - 1   refined: 1 <= x *)
Lemma f3 : 1 <= x -> proot r 2 (x ^+ 2 - 1) = proot r 2 (x - 1) * proot r 2 (x + 1).
Proof. move=> h. radcan. exact: h. Qed.
End Generic.

Local Open Scope R_scope.
Lemma sf1 (x : R) : 1 < x -> sqrt (x ^ 2 - 1) / sqrt (x - 1) = sqrt (x + 1).
Proof. move=> x_gt1. radcan_Rstd. radcan. radcan_Rstd_back. lra. Qed.
```

## Part 11 — the same base under different indices (milestone M5)

`√x` and `∛x` are roots of the same base `x` with different indices. The
normaliser rewrites them over the least common index:
`proot n B ^ e = proot L B ^ (e·L/n)` for `n | L`. It also lowers the index
when it can: `proot 6 B ^ 3 = proot 2 B`. Both rewrites need `0 ≤ B`, which
is recorded as a condition (the same condition as when `B` is split off a
radicand, so it appears only once). Every base ends with a single, fully
reduced index, so both sides of an equality meet.

```coq
Local Open Scope ring_scope.
Section Generic.
Variables (F : numFieldType) (r : posroot F) (x y : F).

(* √x · ∛x = ⁶√(x⁵) *)
Lemma i1 : 0 <= x -> proot r 2 x * proot r 3 x = proot r 6 (x ^+ 5).
Proof. move=> x_ge0. radcan. exact: x_ge0. Qed.

(* raw: 0 <= x, x != 0   refined: 0 < x *)
Lemma i2 : 0 < x -> proot r 2 x / proot r 3 x = proot r 6 x.
Proof. move=> x_gt0. radcan. exact: x_gt0. Qed.

Lemma i3 : 0 <= x -> proot r 4 x ^+ 2 = proot r 2 x.
Proof. move=> x_ge0. radcan. exact: x_ge0. Qed.

Lemma i4 : 0 <= x -> proot r 6 (x ^+ 3) = proot r 2 x.
Proof. move=> x_ge0. radcan. exact: x_ge0. Qed.

Lemma i5 : 1 <= x ->
  proot r 2 (x - 1) * proot r 3 (x - 1) = proot r 6 ((x - 1) ^+ 5).
Proof. move=> x_ge1. radcan. exact: x_ge1. Qed.

(* different bases stay apart, no condition *)
Lemma i6 : proot r 2 2 * proot r 3 x = proot r 3 x * proot r 2 2.
Proof. by radcan. Qed.

Lemma i7 : 0 <= x -> 0 <= y ->
  proot r 2 (x * y) * proot r 3 x = proot r 6 (x ^+ 5) * proot r 2 y.
Proof. move=> x_ge0 y_ge0. radcan. all: by []. Qed.
End Generic.

Local Open Scope R_scope.
(* Stdlib has only sqrt: sqrt (sqrt x) is a root of the atom sqrt x *)
Lemma si1 (x : R) : 0 <= x -> sqrt x * sqrt (sqrt x) = sqrt (sqrt (x ^ 3)).
Proof.
move=> x_ge0. radcan_Rstd. radcan.
(* radcan leaves 0 <= x (0 <= sqrt x follows from it and is dropped) *)
by radcan_Rstd_back; lra.
Qed.
```

## Part 12 — negative radicands (milestone M6)

On ℝ the odd roots of negative numbers exist: `∛(−8) = −2`. On ℂ they do
not behave like this: mathcomp's `3.-root (−8)` is the principal complex
root, not `−2`. So this law is **not** part of `posroot`. It is a separate
record:

```coq
Record oddroot (F : numFieldType) (r : posroot F) : Prop := OddRoot {
  prootN : forall n a, odd n -> proot r n (- a) = - proot r n a }.
```

`rootR` now satisfies it (`rootR_oddroot`). For odd `n` and `a < 0`,
`rootR n a = − rootR n (−a)`; even roots of negatives are still `0`, like
`sqrt`. With an `oddroot` (always for `rootR`; for `proot r` when a
hypothesis `o : oddroot r` is in the context), `radcan` uses a second
checker, `radcan_check_odd`, which simplifies `∛(−c) = −∛c` and
`∛(1−x) = −∛(x−1)`.

For even roots the sign of a base is chosen so that the radicand has a
positive constant: `√(1−x)` keeps the base `1 − x`, with condition
`0 ≤ 1 − x` (refined to `x ≤ 1`). This holds for every `posroot`.

```coq
(* with an oddroot o : oddroot r in the context, radcan uses the odd mode;  *)
(* on rootR it always does (rootR_oddroot)                                   *)

Section Odd.
Variables (F : numFieldType) (r : posroot F) (o : oddroot r) (x : F).

Lemma n1 : proot r 3 (- 8) = - 2.
Proof. by radcan. Qed.

Lemma n2 : proot r 3 (- 2) * proot r 3 (- 4) = 2.
Proof. by radcan. Qed.

Lemma n3 : proot r 3 (- 3) ^+ 3 = - 3.
Proof. by radcan. Qed.

Lemma n4 : proot r 5 (- 32) + 2 = 0.
Proof. by radcan. Qed.

(* the cube root of 1 - x is minus the cube root of x - 1, no condition *)
Lemma n5 : proot r 3 (1 - x) = - proot r 3 (x - 1).
Proof. by radcan. Qed.

(* raw: 0 <= x - 1   refined: 1 <= x *)
Lemma n6 : 1 <= x -> proot r 3 (1 - x) * proot r 3 (x - 1) ^+ 2 = 1 - x.
Proof. move=> x_ge1. radcan. Show. exact: x_ge1. Qed.
End Odd.

Section Even.
Variables (F : numFieldType) (r : posroot F) (x : F).

(* without an oddroot the cube root of -8 is not simplified *)
Goal proot r 3 (- 8) = - 2.
Proof. Fail radcan. Abort.

(* even roots: the base keeps the sign of the radicand  *)
(* raw: 0 <= 1 - x (printed -1 * x + 1)   refined: x <= 1 *)
Lemma e1 : x <= 1 -> proot r 2 (1 - x) ^+ 2 = 1 - x.
Proof. move=> x_le1. radcan. Show. exact: x_le1. Qed.

(* x - 1 is in the basis: sqrt (1 - x) still has base 1 - x *)
(* raw: 0 <= x - 1, 0 <= 1 - x   refined: 1 <= x, x <= 1 *)
Lemma e2 : x = 1 -> proot r 2 (x - 1) ^+ 2 + proot r 2 (1 - x) ^+ 2 = 0.
Proof. move=> x1. radcan. Show. all: by rewrite x1. Qed.

(* sqrt (1 - x) * sqrt (x - 1) = 0 needs x = 1: not found *)
Goal proot r 2 (1 - x) * proot r 2 (x - 1) = 0.
Proof. Fail radcan. Abort.
End Even.

(* on a real closed field, with rootR and its oddroot *)
Lemma rn1 (R : rcfType) : rootR 3 (- 8) = - 2 :> R.
Proof. by radcan. Qed.

Lemma rn2 (R : rcfType) (x : R) : rootR 3 (1 - x) + rootR 3 (x - 1) = 0.
Proof. by radcan. Qed.

(* on C, the principal cube root of -8 is not -2: radcan refuses *)
Goal forall C : numClosedFieldType, 3.-root (-8 : C) = -2.
Proof. move=> C. Fail radcan. Abort.
```

## Part 13 — big numbers and the BigZ/BigQ backend (milestone M4)

The normaliser is written once, as a functor over a module type `NUM` of
integers and rationals (`Backend.v`). It has two instances:

- `RadcanZ` (Stdlib `Z`/`Q`), used by `radcan`;
- `RadcanBig` (Bignums `BigZ`/`BigQ`, on machine integers), used by
  `radcan_big` (`From Radcan Require Import RadcanBig`). A proof made with
  `radcan_big` depends on the axioms of primitive integers; `radcan` does
  not.

Constant radicands are factored by trial division by the primes below 1000.
Each leftover is tested for being a perfect power. A pairwise coprime basis
is built from all the constant radicands of the goal by gcds (the paper's
"form 2"). As always, the factorisation is checked by multiplication, so
none of this needs a proof.

On Stdlib `R`, numerals stay binary all the way: `radcan_Rstd` rewrites
`IZR (Zpos p)` into `pos2F p`, which is exactly how the syntax reads a
constant, and the reifier reads `p` directly. (`Tactic.v` sets the
conversion strategy so that `pos2F` is unfolded last and a numeral is never
expanded in unary.)

```coq
(* big Stdlib numerals: binary all the way, factoring by small primes + gcd basis *)
Lemma b1 : sqrt (1000000007 ^ 2 * 3) = 1000000007 * sqrt 3.
Proof. radcan_Rstd. radcan. Qed.

Lemma b2 : sqrt (1000003 * 1000033) * sqrt 1000003 = 1000003 * sqrt 1000033.
Proof. radcan_Rstd. radcan. Qed.

Lemma b3 : sqrt 1000000007 * sqrt 1000000007 = 1000000007.
Proof. radcan_Rstd. radcan. Qed.

(* the same with the BigZ/BigQ backend *)
Lemma b4 : sqrt (1000003 * 1000033) * sqrt 1000003 = 1000003 * sqrt 1000033.
Proof. radcan_Rstd. radcan_big. Qed.

Lemma b5 : / (sqrt 2 + sqrt 3 + sqrt 5) * (sqrt 2 + sqrt 3 + sqrt 5) = 1.
Proof. radcan_Rstd. radcan_big. Qed.
```

Timings: `b1`–`b3` take about 0.1 s each, including the kernel check. On the
normaliser alone, BigQ is about 6× faster for large inverses
(`1/(∛2+√3+⁵√7)`: 0.61 s with `Q`, 0.105 s with BigQ). The two backends are
about the same on polynomial expansion.

## Part 14 — polynomial gcd and square-free factoring (milestone M7)

Radicands with variables used to be split only by polynomials that appear
literally in the goal. Now `Poly.v` computes:

- `pgcd`, a polynomial gcd over `Q` in any number of variables (main
  variable + content, primitive pseudo-remainder sequence);
- `sqf`, a square-free decomposition (Yun's algorithm: gcd of `P` and `P'`),
  so `x² + 2x + 1` is seen as `(x + 1)²`;
- a coprime basis of all the radicands of the goal (Collins), built from
  these square-free factors by gcds;
- `gcd_split`, used to cancel rational functions through a gcd:
  `(x²−1)/(x²+2x+1) = (x−1)/(x+1)` with condition `x + 1 ≠ 0`.

None of these algorithms is trusted. Each decomposition is checked by
multiplication, so a wrong gcd can only lose a simplification.

```coq
Section Generic.
Variables (F : numFieldType) (r : posroot F) (x y : F).

(* raw: 0 <= x + 1   refined: -1 <= x *)
Lemma g1 : -1 <= x -> proot r 2 (x ^+ 2 + 2 * x + 1) = x + 1.
Proof. move=> h. radcan. exact: h. Qed.

(* raw: 0 <= x - 1   refined: 1 <= x *)
Lemma g2 : 1 <= x ->
  proot r 2 (x ^+ 3 - 3 * x ^+ 2 + 3 * x - 1) = (x - 1) * proot r 2 (x - 1).
Proof. move=> h. radcan. exact: h. Qed.

(* (x^2 - 1)^2: raw 0 <= x ^+ 2 - 1, refined 1 <= x ^+ 2 *)
Lemma g3 : 1 <= x ^+ 2 -> proot r 2 (x ^+ 4 - 2 * x ^+ 2 + 1) = x ^+ 2 - 1.
Proof. move=> h. radcan. exact: h. Qed.

Lemma g4 : -1 <= x ->
  proot r 2 (x ^+ 2 + 2 * x + 1) * proot r 2 (x + 1) = (x + 1) * proot r 2 (x + 1).
Proof. move=> h. radcan. exact: h. Qed.

Lemma g5 : -1 <= x -> proot r 2 (2 * x ^+ 2 + 4 * x + 2) = (x + 1) * proot r 2 2.
Proof. move=> h. radcan. exact: h. Qed.

(* the same base under a cube root *)
Lemma g6 : -1 <= x -> proot r 3 (x ^+ 3 + 3 * x ^+ 2 + 3 * x + 1) = x + 1.
Proof. move=> h. radcan. exact: h. Qed.

(* several variables: the condition is 0 <= x + y *)
Lemma g7 : 0 <= x + y -> proot r 2 (x ^+ 2 + 2 * x * y + y ^+ 2) = x + y.
Proof. move=> h. radcan. first [exact: h | by rewrite addrC]. Qed.

(* y (x + 1)^2: two conditions, 0 <= y and -1 <= x *)
Lemma g8 : 0 <= y -> -1 <= x ->
  proot r 2 (y * x ^+ 2 + 2 * x * y + y) = (x + 1) * proot r 2 y.
Proof. move=> hy hx. radcan. all: by []. Qed.

(* no root: cancellation through gcd (x^2 - 1, x^2 + 2x + 1) = x + 1 *)
(* raw: x + 1 != 0   refined: x != -1 *)
Lemma g9 : x != -1 -> (x ^+ 2 - 1) / (x ^+ 2 + 2 * x + 1) = (x - 1) / (x + 1).
Proof. move=> h. radcan. exact: h. Qed.

Lemma g10 : x + y != 0 ->
  (x ^+ 2 - y ^+ 2) / (x ^+ 2 + 2 * x * y + y ^+ 2) = (x - y) / (x + y).
Proof. move=> h. radcan. first [exact: h | by rewrite addrC]. Qed.
End Generic.

Local Open Scope R_scope.
Lemma sg1 (x : R) : -1 <= x -> sqrt (x ^ 2 + 2 * x + 1) = x + 1.
Proof. move=> h. radcan_Rstd. radcan. radcan_Rstd_back. lra. Qed.

Lemma sg2 (x : R) : x <> -1 -> (x ^ 2 - 1) / (x ^ 2 + 2 * x + 1) = (x - 1) / (x + 1).
Proof. move=> h. radcan_Rstd. radcan. radcan_Rstd_back. lra. Qed.

Lemma sg3 (x y : R) : 0 <= x + y -> sqrt (x ^ 2 + 2 * x * y + y ^ 2) = x + y.
Proof. move=> h. radcan_Rstd. radcan. radcan_Rstd_back. lra. Qed.
```

## Part 15 — refined conditions with several variables (milestone M8)

`Refine.v` now works on polynomials over atoms. An atom is a variable, a
root such as `√x`, or an inverse. The refinement:

- splits products in `≠ 0` conditions into one condition per factor;
- divides a condition by its positive integer content (`0 <= 2x − 2y`
  becomes `y <= x`);
- keeps only the strongest of conditions with the same non-constant part;
- merges `0 <= P` and `P != 0` into `0 < P`;
- prints with the constant and the negative terms on the other side:
  `1 <= x ^+ 2`, `-1 <= x * y`, `x ^+ 2 != 4`, `x + y < 3`.

As before, the refined list is used only if a proved checker shows that it
implies the raw list. Only reasoning valid in any `numFieldType` is used.

```coq
Section Multi.
Variables (F : numFieldType) (r : posroot F) (x y : F).

(* raw: 0 <= y + x, 0 <= -1 * y + x, -1 * y + x != 0
   refined: 0 <= x + y, y < x *)
Lemma g1 : 0 <= x + y -> y < x ->
  proot r 2 (x ^+ 2 - y ^+ 2) / proot r 2 (x - y) = proot r 2 (x + y).
Proof. move=> h1 h2. radcan. all: by []. Qed.

(* the same with y <= x and x != y: y < x is lt_def *)
Lemma g2 : 0 <= x + y -> y <= x -> x != y ->
  proot r 2 (x ^+ 2 - y ^+ 2) / proot r 2 (x - y) = proot r 2 (x + y).
Proof. move=> h1 h2 h3. radcan. - exact: h1. - by rewrite lt_def h3 h2. Qed.

(* raw: 0 <= 2 * x - 2 * y   refined: y <= x  (divided by 2) *)
Lemma g3 : y <= x -> proot r 2 (2 * x - 2 * y) ^+ 2 = 2 * x - 2 * y.
Proof. move=> h. radcan. exact: h. Qed.

(* a constant stays: raw 0 <= 2 * x - 2 * y + 1   refined: 2 * y - 1 <= 2 * x *)
Lemma g4 : 2 * y - 1 <= 2 * x ->
  proot r 2 (2 * x - 2 * y + 1) ^+ 2 = 2 * x - 2 * y + 1.
Proof. move=> h. radcan. exact: h. Qed.

(* not affine: the constant goes to the other side *)
(* raw: 0 <= x * y + 1   refined: -1 <= x * y *)
Lemma g5 : -1 <= x * y ->
  proot r 2 (x * y + 1) * proot r 2 (x * y + 1) = x * y + 1.
Proof. move=> h. radcan. exact: h. Qed.

(* raw: 0 <= x ^+ 2 - 1   refined: 1 <= x ^+ 2 *)
Lemma g6 : 1 <= x ^+ 2 -> proot r 2 (x ^+ 2 - 1) ^+ 2 = x ^+ 2 - 1.
Proof. move=> h. radcan. exact: h. Qed.

(* raw: x ^+ 2 - 4 != 0   refined: x ^+ 2 != 4 *)
Lemma g7 : x ^+ 2 != 4 -> (x ^+ 2 - 4) / (x ^+ 2 - 4) = 1.
Proof. move=> h. radcan. exact: h. Qed.

(* a product is nonzero when its factors are: x * y != 0 gives x != 0 and *)
(* y != 0 (here the normaliser already splits it; Refine.v does it too,   *)
(* e.g. for x ^+ 3 * y != 0, see refine_ex13)                              *)
Lemma g8 : x != 0 -> y != 0 -> (x * y) / (x * y) = 1.
Proof. move=> h1 h2. radcan. all: by []. Qed.

(* the normaliser expands (x - 1) * (x + 1): no factorisation is tried *)
(* raw: x ^+ 2 - 1 != 0   refined: x ^+ 2 != 1 *)
Lemma g9 : x ^+ 2 != 1 -> (x - 1) * (x + 1) / ((x - 1) * (x + 1)) = 1.
Proof. move=> h. radcan. exact: h. Qed.
End Multi.

(* on Stdlib reals the refined conditions are closed by lra *)
Local Open Scope R_scope.
Lemma sg1 (x y : R) : 0 <= x + y -> y < x ->
  sqrt (x ^ 2 - y ^ 2) / sqrt (x - y) = sqrt (x + y).
Proof. move=> h1 h2. radcan_Rstd. radcan. all: radcan_Rstd_back; lra. Qed.
```

## Part 16 — roots of unity on ℂ (milestone M9)

On ℂ, mathcomp's `n.-root` is the principal root. For `a ≥ 0`,
`n.-root (−a) = n.-root a · ω_n`, where `ω_n = n.-root (−1)` satisfies
`ω_n ^+ n = −1`. These are the paper's roots of unity. The laws form a third
record next to `posroot` and `oddroot`:

```coq
Record negroot (F : numFieldType) (r : posroot F) := NegRoot {
  wroot : nat -> F;
  prootNw : forall n a, (0 < n)%N -> 0 <= a -> proot r n (- a) = proot r n a * wroot n;
  wrootK : forall n, (0 < n)%N -> wroot n ^+ n = -1 }.
```

`rootC_negroot C` is the instance for ℂ. `radcan` uses the corresponding
checker, `radcan_check_neg`, by itself on `n.-root` goals, and on `proot r`
goals when a `w : negroot r` is in the context. `ω_n` is reduced only by
`ω_n ^+ n = −1`. This is sound but incomplete: the cyclotomic relation
`ω₃² − ω₃ + 1 = 0` is not used. `ω_4²` and `ω_2` are not identified either,
because the index law for principal roots is not proved.

```coq
(* M9: roots of negative numbers on C through the roots of unity            *)
(* omega_n = n.-root (-1), omega_n ^+ n = -1, and for 0 <= a                 *)
(*   n.-root (- a) = n.-root a * omega_n                                     *)
(* (negroot, PosRoot.v; rootC_negroot C, RootC.v).  The checker is          *)
(* radcan_check_neg, the theorem radcan_eq_refined_neg (NegRootC.v).        *)

(* radcan uses this mode by itself on n.-root goals (rootC_negroot C), and *)
(* on proot r goals when a w : negroot r is in the context                 *)

Section Unity.
Variables (C : numClosedFieldType) (x : C).

(* sqrt (-4) = 2 omega_2 *)
Lemma u1 : 2.-root (-4 : C) = 2 * 2.-root (-1).
Proof. by radcan. Qed.

Lemma u2 : 2.-root (-1 : C) ^+ 2 = -1.
Proof. by radcan. Qed.

(* true for the principal roots: i sqrt 2 * i sqrt 8 = -4 *)
Lemma u3 : 2.-root (-2 : C) * 2.-root (-8) = -4.
Proof. by radcan. Qed.

Lemma u4 : 3.-root (-8 : C) ^+ 3 = -8.
Proof. by radcan. Qed.

(* the principal cube root of -8 is 2 omega_3, not -2 *)
Lemma u5 : 3.-root (-8 : C) = 2 * 3.-root (-1).
Proof. by radcan. Qed.

Goal 3.-root (-8 : C) = -2.
Proof. Fail radcan. Abort.

Lemma u6 : 2.-root (-3 : C) * 2.-root (-3) * 2.-root (-3) = -3 * 2.-root (-3).
Proof. by radcan. Qed.

Lemma u7 : (1 + 2.-root (-1 : C)) ^+ 2 = 2 * 2.-root (-1).
Proof. by radcan. Qed.

(* omega_n ^-1 = - omega_n ^+ (n - 1) *)
Lemma u8 : 1 / 2.-root (-1 : C) = - 2.-root (-1).
Proof. by radcan. Qed.

Lemma u9 : 1 / 3.-root (-2 : C) = - 3.-root (-1) ^+ 2 * 3.-root 4 / 2.
Proof. by radcan. Qed.

(* omega_3 is a root of x^2 - x + 1: found by the cyclotomic reduction     *)
(* (Part 34)                                                                *)
Goal 3.-root (-1 : C) ^+ 2 - 3.-root (-1) + 1 = 0.
Proof. radcan. Qed.

(* omega atoms of different indices are merged by the index law (Part 33) *)
Goal 4.-root (-1 : C) ^+ 2 = 2.-root (-1).
Proof. radcan. Qed.

(* a polynomial radicand with no base to flip:                              *)
(* raw: 0 <= x - 1   refined: 1 <= x                                         *)
Lemma u10 : 1 <= x -> 2.-root (- (x - 1) ^+ 2) = (x - 1) * 2.-root (-1).
Proof. move=> x_ge1. radcan. exact: x_ge1. Qed.

End Unity.

(* with any posroot r and a negroot w in the context *)
Section Generic.
Variables (F : numFieldType) (r : posroot F) (w : negroot r).

Lemma g1 : proot r 2 (- 2) * proot r 2 (- 8) = - 4.
Proof. by radcan. Qed.

End Generic.
```

## Part 17 — cleanups (milestone M10)

Some cancellations were missing, and now work:

- repeated inverse atoms: `x^3 / x^3 = 1`, `x^2 / x^5 = 1 / x^3` (condition `x ≠ 0`);
- inverse atoms are stored primitive, with a positive leading coefficient:
  `1/(2x+2) = (1/2)·1/(x+1)`, `(2x+2)/(3x+3) = 2/3`, `1/(1−x) = −1/(x−1)`;
- division of a numerator containing roots: `(√2·x+√2)/(x+1) = √2`;
- a root common to all terms of a denominator is taken out:
  `1/(√2·x+√2) = √2/(2(x+1))`.

```coq
Section Cleanups.
Variables (F : numFieldType) (r : posroot F) (x y : F).

(* an inverse atom with exponent 3 is cancelled three times *)
(* raw: x != 0 *)
Lemma m1 : x != 0 -> x ^+ 3 / x ^+ 3 = 1.
Proof. move=> h. radcan. exact: h. Qed.

Lemma m2 : x != 0 -> x * x / (x * x) = 1.
Proof. move=> h. radcan. exact: h. Qed.

(* raw: x != 0, y != 0 *)
Lemma m3 : x != 0 -> y != 0 -> (x ^+ 3 * y) / (x ^+ 3 * y) = 1.
Proof. move=> h1 h2. radcan. all: by []. Qed.

(* the same with a root somewhere *)
Lemma m3r : x != 0 -> y != 0 ->
  (x ^+ 3 * y) / (x ^+ 3 * y) = 1 + proot r 2 2 - proot r 2 2.
Proof. move=> h1 h2. radcan. all: by []. Qed.

Lemma m4 : x != 0 -> x ^+ 2 / x = x.
Proof. move=> h. radcan. exact: h. Qed.

Lemma m5 : x != 0 -> x / x ^+ 2 = 1 / x.
Proof. move=> h. radcan. exact: h. Qed.

(* rational coefficients in a radicand: x / 2 - 1 = (x - 2) / 2 *)
(* raw: 0 <= x - 2   refined: 2 <= x *)
Lemma m6 : 2 <= x -> proot r 2 (x / 2 - 1) ^+ 2 = x / 2 - 1.
Proof. move=> h. radcan. exact: h. Qed.

(* inverse atoms are primitive with a positive leading coefficient *)
Lemma m7 : 1 / (2 * x + 2) = 1 / 2 * (1 / (x + 1)).
Proof. radcan. Qed.

Lemma m8 : 1 / (1 - x) = - (1 / (x - 1)).
Proof. radcan. Qed.

(* raw: x + 1 != 0   refined: x != -1 *)
Lemma m9 : x != -1 -> (2 * x + 2) / (x + 1) = 2.
Proof. move=> h. radcan. exact: h. Qed.

Lemma m10 : x != -1 -> (2 * x + 2) / (3 * x + 3) = 2 / 3.
Proof. move=> h. radcan. exact: h. Qed.

(* the inverse of a product is the product of the inverses (no condition) *)
Lemma m11 : 1 / (x * y) = (1 / x) * (1 / y).
Proof. radcan. Qed.

(* a root common to all the terms of a denominator is inverted on its own *)
Lemma m12 : 1 / (proot r 2 2 * x + proot r 2 2) = proot r 2 2 / (2 * (x + 1)).
Proof. radcan. Qed.

(* exact division when the numerator has roots *)
Lemma m13 : x != -1 -> (proot r 2 2 * x + proot r 2 2) / (x + 1) = proot r 2 2.
Proof. move=> h. radcan. exact: h. Qed.

Lemma m14 : x != 0 -> x / (proot r 2 2 * x) = proot r 2 2 / 2.
Proof. move=> h. radcan. exact: h. Qed.
End Cleanups.

(* on Stdlib reals *)
Local Open Scope R_scope.
Lemma sm1 (x : R) : x <> 0 -> x ^ 3 / x ^ 3 = 1.
Proof. move=> h. radcan_Rstd. radcan. radcan_Rstd_back. exact: h. Qed.

Lemma sm2 (x : R) : 2 <= x -> sqrt (x / 2 - 1) ^ 2 = x / 2 - 1.
Proof. move=> h. radcan_Rstd. radcan. radcan_Rstd_back. lra. Qed.

Lemma sm3 (x : R) : x <> -1 -> (2 * x + 2) / (x + 1) = 2.
Proof. move=> h. radcan_Rstd. radcan. radcan_Rstd_back. lra. Qed.
```

## Part 18 — rationalising denominators with variables and roots (milestone M11)

A denominator `d` that mixes variables and roots, such as `√x + √y` or
`x + √2 + ∛9`, used to stay an opaque atom `d⁻¹`. Now `Ratio.v` computes
`u` and a root-free polynomial `E` with `d · u = E`:

1. the root monomials of `d` (roots of numbers and of polynomials) give a
   basis, and multiplication by `d` is a matrix whose entries are
   polynomials in the variables;
2. a fraction-free Gauss–Jordan (Bareiss) elimination gives `E = det` and
   `u`; `E` is made primitive with a positive leading coefficient and a
   common factor of `u` and `E` is removed;
3. `d · u = E` is **checked** by the normaliser, conditions included. The
   only new lemma is `d · u = E → E ≠ 0 → d⁻¹ = u · E⁻¹`.

`E ≠ 0` is a new condition. It does not follow from `d ≠ 0`: for `√x + √y`
at `x = y = 1`, `d = 2` but `E = x − y = 0`. To avoid adding this
condition to goals that do not need it, rationalisation is a fallback:
`radcan_check` first normalises without it, and only if the normal forms
differ does it rationalise every mixed denominator on both sides.

```coq
Section Rational.
Variables (F : numFieldType) (r : posroot F) (x y : F).
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).

(* the paper's (1) as a quotient *)
(* raw: 0 <= x, 0 <= y, -1 * y + x != 0   refined: 0 <= x, 0 <= y, x != y *)
Lemma q1 : 0 <= x -> 0 <= y -> x != y ->
  (x - y) / (\sqrt x + \sqrt y) = \sqrt x - \sqrt y.
Proof. move=> hx hy hxy. radcan. all: by []. Qed.

(* refined: 0 <= x, x != 1 *)
Lemma q2 : 0 <= x -> x != 1 -> 1 / (1 + \sqrt x) = (1 - \sqrt x) / (1 - x).
Proof. move=> hx h1. radcan. all: by []. Qed.

(* refined: x ^+ 2 != 2 *)
Lemma q3 : x ^+ 2 != 2 -> 1 / (x + \sqrt 2) = (x - \sqrt 2) / (x ^+ 2 - 2).
Proof. move=> h. radcan. exact: h. Qed.

(* the paper's (3), with the right E (108 x, not 54 x) *)
Lemma q4 : 108 * x + 12 * x ^+ 2 + 18 * x ^+ 3 + x ^+ 6 != 6 * x ^+ 4 - 73 ->
  1 / (x + \sqrt 2 + proot r 3 9) =
  (- (x + \sqrt 2) * proot r 3 9 + 3 * proot r 3 3 +
     (x ^+ 2 + 2 * \sqrt 2 * x + 2)) *
  (x ^+ 3 + 6 * x + 9 - (3 * x ^+ 2 + 2) * \sqrt 2) /
  (x ^+ 6 - 6 * x ^+ 4 + 18 * x ^+ 3 + 12 * x ^+ 2 + 108 * x + 73).
Proof. move=> h. radcan. exact: h. Qed.

Lemma q5 : 0 <= x -> 0 <= y -> x != y ->
  (\sqrt x + \sqrt y) / (\sqrt x - \sqrt y) =
  (x + y + 2 * \sqrt x * \sqrt y) / (x - y).
Proof. move=> hx hy hxy. radcan. all: by []. Qed.
End Rational.

(* on Stdlib reals *)
Local Open Scope R_scope.
Lemma sq1 (x y : R) : 0 <= x -> 0 <= y -> x <> y ->
  (x - y) / (sqrt x + sqrt y) = sqrt x - sqrt y.
Proof. move=> hx hy hxy. radcan_Rstd. radcan. all: radcan_Rstd_back; lra. Qed.

Lemma sq2 (x : R) : x ^ 2 <> 2 -> 1 / (x + sqrt 2) = (x - sqrt 2) / (x ^ 2 - 2).
Proof. move=> h. radcan_Rstd. radcan. radcan_Rstd_back. lra. Qed.
```

## Part 19 — intervals and combined bounds (milestone M12)

The refinement now:

- shows a lower and an upper bound on the same variable as one interval,
  `1 <= x <= 3` (or `1 <= x < 3`);
- drops a raw condition that follows from **several** refined ones. The
  multipliers are found by a small Fourier–Motzkin elimination (unproved),
  then checked by a proved checker: the raw polynomial must equal a
  nonnegative combination of refined conditions plus a nonnegative constant.
  For example `0 < x + y − 2` follows from `1 <= x` and `2 <= y`, since
  `x + y − 2 = (x − 1) + (y − 2) + 1`;
- keeps contradictory bounds such as `3 <= x <= 1` as they are, so you see
  an unprovable goal rather than a crash.

On Stdlib reals, `radcan_Rstd_back` splits an interval into two goals for
`lra`.

```coq
Section Bounds.
Variables (F : numFieldType) (r : posroot F) (x y : F).

(* raw: 0 <= x - 1, 0 <= -1 * x + 3   refined: 1 <= x <= 3 *)
Lemma h1 : 1 <= x <= 3 ->
  proot r 2 (x - 1) * proot r 2 (3 - x) = proot r 2 (- x ^+ 2 + 4 * x - 3).
Proof. move=> h. radcan. exact: h. Qed.

(* a strict side: raw 0 <= x - 1, 0 <= -1 * x + 3, x - 3 != 0
   refined: 1 <= x < 3 *)
Lemma h2 : 1 <= x < 3 ->
  proot r 2 (x - 1) ^+ 2 * proot r 2 (3 - x) ^+ 2 / (3 - x) = x - 1.
Proof. move=> h. radcan. exact: h. Qed.

(* 0 <= 4 - x follows from x <= 3: raw 0 <= x - 1, 0 <= 3 - x, 0 <= 4 - x
   refined: 1 <= x <= 3 *)
Lemma h3 : 1 <= x <= 3 ->
  proot r 2 (x - 1) ^+ 2 + proot r 2 (3 - x) ^+ 2 + proot r 2 (4 - x) ^+ 2
  = 6 - x.
Proof. move=> h. radcan. exact: h. Qed.

(* combinations: x + y - 2 = (x - 1) + (y - 2) + 1, so 0 < x + y - 2
   follows from 1 <= x and 2 <= y
   raw: 0 <= y + (x - 2), y + (x - 2) != 0, 0 <= x - 1, 0 <= y - 2
   refined: 1 <= x, 2 <= y *)
Lemma h4 : 1 <= x -> 2 <= y ->
  proot r 2 (x + y - 2) / proot r 2 (x + y - 2) * proot r 2 (x - 1)
  * proot r 2 (y - 2) = proot r 2 ((x - 1) * (y - 2)).
Proof. move=> hx hy. radcan. all: by []. Qed.

(* only true combinations: 1 <= x and 2 <= y do not give 3 < x + y *)
(* refined: 1 <= x, 2 <= y, 3 < x + y *)
Lemma h5 : 1 <= x -> 2 <= y -> 3 < x + y ->
  proot r 2 (x + y - 3) / proot r 2 (x + y - 3) * proot r 2 (x - 1)
  * proot r 2 (y - 2) = proot r 2 ((x - 1) * (y - 2)).
Proof. move=> hx hy hxy. radcan. all: by []. Qed.

(* contradictory bounds are kept as they are: the goal 3 <= x <= 1 *)
(* cannot be proved                                                   *)
Goal proot r 2 (x - 3) * proot r 2 (1 - x) = proot r 2 (- x ^+ 2 + 4 * x - 3).
Proof. radcan. Abort.
End Bounds.

(* on Stdlib reals the interval is split, each side closed by lra *)
Local Open Scope R_scope.
Lemma sh1 (x : R) : 1 <= x <= 3 ->
  sqrt (x - 1) * sqrt (3 - x) = sqrt (- x ^ 2 + 4 * x - 3).
Proof.
move=> h. radcan_Rstd. radcan.
all: radcan_Rstd_back; lra.
Qed.
```

## Part 20 — nested radicands, absolute values, odd roots on real fields (milestone M13)

- **Nested radicands.** A radicand containing roots is normalised first. If
  the result has no root left, it is treated as a polynomial radicand: this
  is the paper's §2 example `√(x²+3x+3+√(x+1)√(x+1)) = x + 2`.
- **Real fields.** A record `realroot r` (`RealRoot.v`) says that every
  element is real and odd roots exist; `rootR_realroot R` is the instance
  for real closed fields. Then:
  - even roots of even powers are absolute values, with **no** condition:
    `√((x−2)²) = |x−2|`, and `|x|` is read as `√(x²)`;
  - odd roots split and reduce with no sign condition: `∛(−8x³) = −2x`,
    `∛(xy) = ∛x·∛y`.
- `radcan` uses this real mode by itself on `rootR` goals, and on `proot r`
  goals when a `realroot r` is in the context. On Stdlib reals, `Rabs` is
  translated by `radcan_Rstd`.
- **The paper's (4) = (6)** was a real gap on ℂ: with `ω = 3.-root(−1)` it is
  true for principal roots and now proved; read with a 6th root of `−1` it
  is false and refused.

```coq
Section Nested.
Variables (F : numFieldType) (r : posroot F) (x : F).
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).

(* the paper's nested example (section 2):                                  *)
(* raw: 0 <= x + 1, 0 <= x + 2   refined: -1 <= x                           *)
Lemma nest1 : -1 <= x ->
  \sqrt (x ^+ 2 + 3 * x + 3 + \sqrt (x + 1) * \sqrt (x + 1)) = x + 2.
Proof. move=> h. radcan. exact: h. Qed.

(* the inner radicand is a square too *)
Lemma nest2 : 0 <= x ->
  \sqrt (\sqrt (x ^+ 2) * \sqrt (x ^+ 2)) = x.
Proof. move=> h. radcan. exact: h. Qed.
End Nested.

Section Real.
Variables (R : rcfType) (x y : R).

(* no condition: even roots of even powers are absolute values *)
Lemma a1 : rootR 2 ((x - 2) ^+ 2) = `|x - 2|.
Proof. by radcan. Qed.

Lemma a2 : rootR 2 (x ^+ 2) = `|x|.
Proof. by radcan. Qed.

Lemma a3 : rootR 2 (x ^+ 2 * y ^+ 2) = `|x| * `|y|.
Proof. by radcan. Qed.

Lemma a4 : rootR 2 (x ^+ 2) ^+ 2 = x ^+ 2.
Proof. by radcan. Qed.

(* the radicand x^2 - 4x + 4 is seen as (x - 2)^2 *)
Lemma a5 : rootR 2 (x ^+ 2 - 4 * x + 4) = `|x - 2|.
Proof. by radcan. Qed.

Lemma a6 : rootR 2 (4 * x ^+ 2) = 2 * `|x|.
Proof. by radcan. Qed.

Lemma a7 : `|x| ^+ 2 = x ^+ 2.
Proof. by radcan. Qed.

Lemma a8 : rootR 4 (x ^+ 4) = `|x|.
Proof. by radcan. Qed.

(* |B| is not B: with |x|, sqrt (x^2) = x is refused, then retried with  *)
(* x and the condition 0 <= x (refined: 0 <= x)                          *)
Lemma a9 : 0 <= x -> rootR 2 (x ^+ 2) = x.
Proof. move=> h. radcan. exact: h. Qed.

(* odd roots of any sign: no condition *)
Lemma o1 : rootR 3 (x ^+ 3) = x.
Proof. by radcan. Qed.

Lemma o2 : rootR 3 (- 8 * x ^+ 3) = - 2 * x.
Proof. by radcan. Qed.

Lemma o3 : rootR 3 (x * y) = rootR 3 x * rootR 3 y.
Proof. by radcan. Qed.

Lemma o4 : rootR 3 (x ^+ 2) * rootR 3 x = x.
Proof. by radcan. Qed.

Lemma o5 : rootR 3 x * rootR 5 x = rootR 15 (x ^+ 8).
Proof. by radcan. Qed.

(* the odd mode (oddroot only) still asks 0 <= x *)
Lemma o6 : 0 <= x -> rootR 3 (x ^+ 3) = x.
Proof.
move=> h. radcan_with_gen true (rootR_posroot R) (rootR_oddroot R). exact: h.
Qed.
End Real.

(* any posroot on a realFieldType with an oddroot gives a realroot *)
Section RealField.
Variables (F : realFieldType) (r : posroot F) (o : oddroot r) (x : F).
Let rl := realroot_of o.

Lemma f1 : proot r 2 ((x + 1) ^+ 2) = `|x + 1|.
Proof. by radcan. Qed.

Lemma f2 : proot r 3 (- x ^+ 3) = - x.
Proof. by radcan. Qed.
End RealField.

(* the paper's (4) = (6) on C, with omega = 3.-root (-1) (the paper prints *)
(* omega_6 for (-1)^(1/3) = omega_6 ^+ 2 in its convention); raw and      *)
(* conditions: raw 0 <= x ^+ 2 + 1, refined -1 <= x ^+ 2                   *)
Section Paper46.
Variables (C : numClosedFieldType) (x : C).

Lemma eq46 : -1 <= x ^+ 2 ->
  (4.-root 2 + 2.-root 3 * 3.-root (- (x ^+ 2 + 1))) / 2.-root (x ^+ 2 + 1) =
  1 / (x ^+ 2 + 1) * 4.-root 2 * 6.-root (x ^+ 2 + 1) ^+ 3 +
  1 / (x ^+ 2 + 1) * 3.-root (-1) * 2.-root 3 * 6.-root (x ^+ 2 + 1) ^+ 5.
Proof. move=> h. radcan. exact: h. Qed.

(* with a 6th root of -1 it is false (at x = 0 it says                     *)
(* 3.-root (-1) = 6.-root (-1), but their 6th powers are 1 and -1)         *)
Goal (4.-root 2 + 2.-root 3 * 3.-root (- (x ^+ 2 + 1))) / 2.-root (x ^+ 2 + 1) =
  1 / (x ^+ 2 + 1) * 4.-root 2 * 6.-root (x ^+ 2 + 1) ^+ 3 +
  1 / (x ^+ 2 + 1) * 6.-root (-1) * 2.-root 3 * 6.-root (x ^+ 2 + 1) ^+ 5.
Proof. Fail radcan. Abort.
End Paper46.
```

## Part 21 — `radcan_simplify` (milestone M17)

`radcan_simplify` is the analogue of `ring_simplify`: it replaces each side of
the goal (or of a hypothesis) by its normal form, printed back as a readable
mathcomp expression, and leaves the side conditions as goals after the main
one.

- The printer needs no proof. The tactic proves `e = e'` with the usual
  checker, which normalises the printed `e'` again; that also checks that
  printing is stable.
- Printing rules:
  - higher powers come first and constants last;
  - negative terms are written as subtractions, and the coefficient 1 is
    omitted;
  - terms sharing an inverse go over one common denominator;
  - `proot n a ^+ k` is shown as `proot n (a ^+ k)` only when this adds no
    condition.
- The display is cleaned: numerals are shown as numerals, and `n.-root` or
  `rootR` are used according to the goal. The atoms are renumbered so that
  running it twice changes nothing.
- Forms: `radcan_simplify`, `radcan_simplify in H`, and
  `radcan_simplify_term t` (only the subterm `t`), with `_raw` versions that
  keep the raw conditions. Supported goals are `a = b`, `a <> b`, `a != b`
  and `a <= b`, `a < b`, `a == b`.

| Input | Result | Side conditions |
|---|---|---|
| `√12 − √3` | `√3` | |
| `1/(1+√2)` | `√2 − 1` | |
| `(1+√2)²` | `2√2 + 3` | |
| `√(x²+2x+1)` | `x + 1` | `-1 <= x` |
| `(x−y)/(√x+√y)` | `√x − √y` | `0 <= x`, `0 <= y`, `x != y` |
| `(√x+√y)/(√x−√y)` | `(x + y + 2√x√y)/(x − y)` | `0 <= x`, `0 <= y`, `x != y` |
| `√x · ∛x` | `⁶√(x⁵)` | `0 <= x` |
| `H : y = √8 · √2` (`in H`) | `H : y = 4` | |
| `√12 + x <= √27` | `x + 2√3 <= 3√3` | |
| ℂ: `√(−4) + ∛16 − ∛2` | `2·√(−1) + ∛2` | |

On real closed fields (`rootR`, or a `realroot` in the context) it uses the
real mode of Part 20 and shows absolute values:

| Input | Result |
|---|---|
| `rootR 2 ((x−2)²)` | `` `|x − 2|`` |
| `rootR 2 (x²·y²)` | `` `|x| * `|y|`` |
| `rootR 3 (−8x³)` | `- (2 * x)` (no condition) |
| `rootR 2 (4x²) + `|x|` | `` 3 * `|x|`` |

See `tutorial/Tut21_simplify.v`, where each example also checks stability.

## Part 22 — `radcan_lra` on Stdlib reals (milestone M14)

`radcan_lra` chains `radcan_Rstd`, `radcan`, and, on each side condition,
`radcan_Rstd_back; lra`. The conditions `lra` proves from the hypotheses
disappear, and the others are left as goals.

```coq
Lemma l1 (x : R) : 1 < x -> sqrt (x ^ 2 - 1) / sqrt (x - 1) = sqrt (x + 1).
Proof. move=> h. radcan_lra. Qed.

Lemma l2 (x : R) : 1 <= x <= 3 ->
  sqrt (x - 1) * sqrt (3 - x) = sqrt (- x ^ 2 + 4 * x - 3).
Proof. move=> h. radcan_lra. Qed.

Lemma l3 : sqrt 12 - sqrt 3 = sqrt 3.
Proof. radcan_lra. Qed.

(* the condition x ^+ 2 != 2 is closed by lra from the hypothesis *)
Lemma l4 (x : R) : x ^ 2 <> 2 -> 1 / (x + sqrt 2) = (x - sqrt 2) / (x ^ 2 - 2).
Proof. move=> h. radcan_lra. Qed.

(* two conditions, both closed by lra from the hypotheses *)
Lemma l5 (x : R) : 0 <= x -> x <> 1 ->
  1 / (1 + sqrt x) = (1 - sqrt x) / (1 - x).
Proof. move=> h1 h2. radcan_lra. Qed.

(* without a hypothesis the condition 0 <= x is left as a goal *)
Goal forall x : R, sqrt (x ^ 2) = x.
Proof. move=> x. radcan_lra. Abort.
```

## Part 23 — irreducible factors of radicands (milestone M16)

`IrrFactor.v` factors one-variable polynomials over ℤ (Berlekamp modulo a
small prime, Hensel lifting, Zassenhaus recombination). `MFactor.v` and
`MFactorEEZ.v` factor polynomials in several variables (homogeneous
polynomials, factors linear in some variable, and Wang's EEZ algorithm). All
of this is unproved computation; every factorisation is checked by
multiplication.

The factors are used in the radicand basis only as a fallback, because
splitting a radicand strengthens the conditions (`0 <= x−1`, `0 <= x+1`
instead of `0 <= x²−1`). In practice the square-free coprime basis of Part 14
already proves these goals; the irreducible factors mostly change the
*displayed* normal form (the paper's "form 1").

```coq
Section Generic.
Variables (F : numFieldType) (r : posroot F) (x y : F).
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).

(* raw: 0 <= x + 1, 0 <= x - 1   refined: 1 <= x *)
Lemma f1 : 1 <= x -> \sqrt (x ^+ 2 - 1) = \sqrt (x - 1) * \sqrt (x + 1).
Proof. move=> h. radcan. exact: h. Qed.

(* x^4 - 1 = (x^2 - 1)(x^2 + 1): refined 1 <= x ^+ 2 *)
Lemma f2 : 1 <= x ^+ 2 ->
  \sqrt (x ^+ 4 - 1) / \sqrt (x ^+ 2 + 1) = \sqrt (x ^+ 2 - 1).
Proof. move=> h. radcan. exact: h. Qed.

(* two variables: x^2 - y^2 = (x - y)(x + y) *)
Lemma f3 : y <= x -> 0 <= x + y ->
  \sqrt (x ^+ 2 - y ^+ 2) = \sqrt (x - y) * \sqrt (x + y).
Proof. move=> h1 h2. radcan. all: by []. Qed.

(* x^3 - y^3 = (x - y)(x^2 + x y + y^2) *)
Lemma f4 : y < x -> 0 <= x * y + x ^+ 2 + y ^+ 2 ->
  \sqrt (x ^+ 3 - y ^+ 3) / \sqrt (x - y) = \sqrt (x ^+ 2 + x * y + y ^+ 2).
Proof. move=> h1 h2. radcan. all: by []. Qed.

(* x y + x + y + 1 = (x + 1)(y + 1) *)
Lemma f5 : -1 <= x -> -1 <= y ->
  \sqrt (x * y + x + y + 1) = \sqrt (x + 1) * \sqrt (y + 1).
Proof. move=> h1 h2. radcan. all: by []. Qed.

(* the paper's form 1: (x + 3)^2 (x + 1)(x + 2), refined -1 <= x *)
Lemma f6 : -1 <= x ->
  \sqrt (x ^+ 4 + 9 * x ^+ 3 + 29 * x ^+ 2 + 39 * x + 18) =
  (x + 3) * \sqrt (x + 1) * \sqrt (x + 2).
Proof. move=> h. radcan. exact: h. Qed.

(* no factor of degree 1 in any variable (Wang's EEZ in MFactorEEZ) *)
(* refined: -1 <= 210 * x ^+ 2 + y ^+ 3, -11 <= x ^+ 2 + 2 * y ^+ 2 *)
Lemma f7 : -1 <= 210 * x ^+ 2 + y ^+ 3 -> -11 <= x ^+ 2 + 2 * y ^+ 2 ->
  \sqrt (210 * x ^+ 4 + 420 * x ^+ 2 * y ^+ 2 + 2311 * x ^+ 2 +
         x ^+ 2 * y ^+ 3 + 2 * y ^+ 5 + 11 * y ^+ 3 + 2 * y ^+ 2 + 11) =
  \sqrt (210 * x ^+ 2 + y ^+ 3 + 1) * \sqrt (x ^+ 2 + 2 * y ^+ 2 + 11).
Proof. move=> h1 h2. radcan. all: by []. Qed.
End Generic.

(* the normal form itself: form 2 keeps sqrt (x^2 + 3x + 2), the           *)
(* irreducible basis (form 1) gives sqrt (x + 1) * sqrt (x + 2)              *)
Definition P1 : rexpr :=
  RAdd (RAdd (RAdd (RAdd (RPow (RVar 0) 4) (RMul (RCst 9) (RPow (RVar 0) 3)))
                   (RMul (RCst 29) (RPow (RVar 0) 2)))
             (RMul (RCst 39) (RVar 0))) (RCst 18).
Definition sqP1 := RRootE 2 P1.
Compute nf_to_rexpr (radcan_nf MStd sqP1 sqP1).1.1.
Compute
  let hs := neg_hints [:: sqP1] in
  let bs := irr_basis (mk_basis_n false MStd hs [:: sqP1]) in
  nf_to_rexpr (radcan_nfb false MStd hs bs sqP1 sqP1).1.1.

(* on Stdlib reals the refined conditions are closed by lra *)
Local Open Scope R_scope.
Lemma sf1 (x : R) : 1 <= x -> sqrt (x ^ 2 - 1) = sqrt (x - 1) * sqrt (x + 1).
Proof. move=> h. radcan_Rstd. radcan. all: radcan_Rstd_back; lra. Qed.

Lemma sf2 (x y : R) : y <= x -> 0 <= x + y ->
  sqrt (x ^ 2 - y ^ 2) = sqrt (x - y) * sqrt (x + y).
Proof. move=> h1 h2. radcan_Rstd. radcan. all: radcan_Rstd_back; lra. Qed.
```

## Part 24 — a variable out of a denominator (milestone M18)

When every term of a denominator contains the same variables (a common
monomial `g`), the denominator `d = g·d'` is inverted in two pieces,
`d⁻¹ = g⁻¹ · d'⁻¹`, after checking `d = g·d'` by multiplication. So
`1/(x²+x)` becomes `1/x · 1/(x+1)`, and cancellations then work on each
piece separately. Only plain variables are taken out when the denominator
contains roots.

```coq
Section Denom.
Variables (F : numFieldType) (r : posroot F) (x y : F).
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).

(* the inverse of a product is the product of the inverses: no condition *)
Lemma t1 : 1 / (x ^+ 2 + x) = 1 / x * (1 / (x + 1)).
Proof. radcan. Qed.

Lemma t2 : 1 / (x * y + x) = 1 / x * (1 / (y + 1)).
Proof. radcan. Qed.

(* exponents: x ^+ 2 is taken out *)
Lemma t3 : 1 / (x ^+ 3 + 2 * x ^+ 2) = 1 / x ^+ 2 * (1 / (x + 2)).
Proof. radcan. Qed.

(* cancellation of x + 1 only *)
(* raw: x + 1 != 0   refined: x != -1 *)
Lemma t4 : x != -1 -> (x + 1) / (x ^+ 2 + x) = 1 / x.
Proof. move=> h. radcan. exact: h. Qed.

(* raw: x != 0, y != 0 *)
Lemma t5 : x != 0 -> y != 0 ->
  (x ^+ 2 * y) / (x ^+ 3 * y + x ^+ 2 * y) = 1 / (x + 1).
Proof. move=> hx hy. radcan. all: by []. Qed.

(* with roots: the monomial x, then the root monomial sqrt 2 *)
Lemma t6 : \sqrt 2 / (x ^+ 2 * \sqrt 2 + x) =
  \sqrt 2 / x * (1 / (\sqrt 2 * x + 1)).
Proof. radcan. Qed.

Lemma t7 : \sqrt 2 / (x ^+ 2 * \sqrt 2 + x * \sqrt 2) = 1 / x * (1 / (x + 1)).
Proof. radcan. Qed.

(* a common inverse atom (root-free path) *)
Lemma t8 : 1 / (x / (y + 1) + 1 / (y + 1)) = (y + 1) / (x + 1).
Proof. radcan. Qed.
End Denom.

(* on Stdlib reals *)
Local Open Scope R_scope.
Lemma st1 (x : R) : x <> -1 -> (x + 1) / (x ^ 2 + x) = 1 / x.
Proof. move=> h. radcan_lra. Qed.

Lemma st2 (x y : R) : 1 / (x * y + x) = 1 / x * (1 / (y + 1)).
Proof. radcan_lra. Qed.

Print Assumptions t6.  (* Closed under the global context *)
```

## Part 25 — denesting square roots (milestone M19)

`√(3 + 2√2) = 1 + √2`: a radicand `a + b√c` (rational `a`, `b`) denests
when `a² − b²c = d²` is a rational square; the candidate is
`√((a+d)/2) ± √((a−d)/2)`. The candidate is found without proof, then
checked: its square must normalise to the radicand, and it must be
nonnegative, which is proved by a small certificate (rational bounds on each
square root, checked by integer arithmetic). Then `proot_eq` gives the
equality.

Later phases extend the same check-a-candidate scheme:

- with variables (`√(x + 2√(x−1)) = 1 + √(x−1)`, leaving `1 <= x`): the
  candidate comes from `a² − b²c = d²` as polynomials, and its sign becomes a
  condition, usually implied by conditions already present;
- several inner roots (`√(10+2√6+2√10+2√15) = √2+√3+√5`): the candidate
  `√p + √q + √r` is found by matching the cross terms `2√(pq)`, …;
- several inner roots with variables
  (`√(x+y+z+2√(xy)+2√(xz)+2√(yz)) = √x+√y+√z`).

All of them run inside `radcan` through the composed pre-pass (Part 29).

```coq
(* one nested root: reify its radicand t, find the candidate c, check
   denest_ok e c by vm_compute (the square by radcan_check, the sign by
   sq_nonneg), then rewrite with denest_sound: proot r 2 t = candidate *)
Ltac denest_at r :=
  match goal with
  | |- context [proot r 2 ?t] =>
    let T := type of t in
    let p := radcan_reify_term r t (@nil T) in
    lazymatch p with (?e, ?env) =>
      let c := eval vm_compute in (denest_find e) in
      lazymatch c with
      | Some ?c =>
        let H := fresh "H" in let h := fresh "h" in
        (have H : denest_ok e c by vm_compute);
        have h : proot r 2 t = rinterp r env (dc_rexpr c) :=
          denest_sound r env H;
        rewrite h {h H} /dc_rexpr /=
      end
    end
  end.

(* the whole goal at once: radcan_check on the denested sides *)
Ltac radcan_denest r :=
  radcan_reify r;
  lazymatch goal with
  | |- rinterp _ ?env ?e1 = rinterp _ _ ?e2 =>
    let c := eval vm_compute in (radcan_check_denest e1 e2) in
    lazymatch c with
    | Some ?cs =>
      apply: (@radcan_eq_denest _ r env e1 e2 cs);
        [vm_compute; reflexivity | radcan_split_conds]
    | None => fail "radcan_denest: the normal forms differ"
    end
  end.

Section Denest.
Variables (F : numFieldType) (r : posroot F).

(* plain radcan cannot do it: proot r 2 (3 + 2 sqrt 2) stays an atom *)
Goal proot r 2 (3 + 2 * proot r 2 2) = 1 + proot r 2 2.
Proof. Fail radcan. Abort.

Lemma d1 : proot r 2 (3 + 2 * proot r 2 2) = 1 + proot r 2 2.
Proof. denest_at r. radcan. Qed.

Lemma d2 : proot r 2 (5 + 2 * proot r 2 6) = proot r 2 2 + proot r 2 3.
Proof. denest_at r. radcan. Qed.

(* sign certificate: sqrt 3 - 1 >= 0 needs sqrt 3 >= 1 *)
Lemma d3 : proot r 2 (4 - 2 * proot r 2 3) = proot r 2 3 - 1.
Proof. denest_at r. radcan. Qed.

Lemma d4 : proot r 2 (7 - 4 * proot r 2 3) = 2 - proot r 2 3.
Proof. denest_at r. radcan. Qed.

(* rational coefficients: sqrt (3/2 + sqrt 2) = 1 + sqrt 2 / 2 *)
Lemma d5 : proot r 2 (3 / 2 + proot r 2 2) = 1 + proot r 2 2 / 2.
Proof. denest_at r. radcan. Qed.

(* the whole-goal version, several nested roots *)
Lemma d6 : proot r 2 (3 + 2 * proot r 2 2) - proot r 2 (3 - 2 * proot r 2 2)
  = 2.
Proof. radcan_denest r. Qed.

Lemma d7 : proot r 2 (12 + 6 * proot r 2 3) * proot r 2 (4 - 2 * proot r 2 3)
  = 2 * proot r 2 3.
Proof. radcan_denest r. Qed.

(* sqrt (1 + sqrt 2) does not denest: 1 - 2 = -1 is not a square *)
Goal proot r 2 (1 + proot r 2 2) = 0.
Proof. Fail denest_at r. Abort.

(* it stays as it is, and radcan_denest still proves what radcan proves *)
(* (the condition 0 <= sqrt 2 + 1 of the square of a root is left) *)
Lemma d8 : proot r 2 (1 + proot r 2 2) ^+ 2 = 1 + proot r 2 2.
Proof. radcan_denest r. by rewrite addr_ge0 ?proot_ge0. Qed.

(* a wrong candidate is refused: sqrt (4 - 2 sqrt 3) is not 1 - sqrt 3 *)
Goal proot r 2 (4 - 2 * proot r 2 3) = 1 - proot r 2 3.
Proof. Fail radcan_denest r. Abort.

End Denest.

(* on a real closed field, with rootR *)
Lemma rc_denest (R : rcfType) :
  rootR 2 (5 - 2 * rootR 2 6) = rootR 2 3 - rootR 2 (2 : R).
Proof. radcan_denest (rootR_posroot R). Qed.
```

## Part 26 — roots of fractions (milestone M20)

The paper's rule (i): `√(P/Q) = √P / √Q` when `0 <= P` and `0 <= Q`.
`frac_split` rewrites every root of a fraction containing a variable into
the quotient of the roots and records these two conditions (none for an odd
root on a real field). `radcan` uses it as a fallback when the plain check
fails, so goals it proved before keep their conditions.

```coq
(* radcan_with_gen of Tactic.v, with frac_split before the checker *)
(* radcan falls back to frac_split when the plain check fails *)

Section Generic.
Variables (F : numFieldType) (r : posroot F) (x y z : F).
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).

(* plain radcan fails: the radicand (x - 1) / (x + 2) is one opaque atom   *)
(* raw: 0 <= x - 1, 0 <= x + 2 (twice)   refined: 1 <= x                    *)
Lemma f1 : 1 <= x -> \sqrt ((x - 1) / (x + 2)) = \sqrt (x - 1) / \sqrt (x + 2).
Proof. move=> h. radcan. exact: h. Qed.

Lemma f1r : 0 <= x - 1 -> 0 <= x + 2 ->
  \sqrt ((x - 1) / (x + 2)) = \sqrt (x - 1) / \sqrt (x + 2).
Proof. move=> h1 h2. radcan_raw. all: by []. Qed.

(* refined: 0 <= x, 0 < y *)
Lemma f2 : 0 <= x -> 0 < y -> \sqrt (x / y) * \sqrt y = \sqrt x.
Proof. move=> hx hy. radcan. all: by []. Qed.

(* a lone inverse: 1 / x is 1 * x^-1; refined: 0 <= x *)
Lemma f3 : 0 <= x -> \sqrt (1 / x) = 1 / \sqrt x.
Proof. move=> h. radcan. exact: h. Qed.

Lemma f3b : 0 <= x -> \sqrt (x^-1) = (\sqrt x)^-1.
Proof. move=> h. radcan. exact: h. Qed.

(* the paper's (9): ((x^2 - 1) / (x + 2))^(1/2) / (x^2 + 3x + 2)^(1/3)     *)
(* refined: 1 <= x (1 <= x ^+ 2 follows from it and is dropped)            *)
Lemma f4 : 1 <= x ->
  \sqrt ((x ^+ 2 - 1) / (x + 2)) / proot r 3 (x ^+ 2 + 3 * x + 2) =
  \sqrt (x - 1) * \sqrt (x + 1) / \sqrt (x + 2) /
  (proot r 3 (x + 1) * proot r 3 (x + 2)).
Proof.
move=> h. radcan; exact: h.
Qed.

(* products and powers in the fraction, roots in the radicand *)
Lemma f5 : 0 <= x -> 0 <= y -> 0 <= z ->
  \sqrt (x * y / (z * x ^+ 2)) = \sqrt y / (\sqrt z * \sqrt x).
Proof.
move=> hx hy hz. radcan.
all: by rewrite ?mulr_ge0 ?exprn_ge0.
Qed.

Lemma f6 : 0 <= x -> 0 <= y ->
  \sqrt ((x / y) ^+ 3) = \sqrt x * x / (\sqrt y * y).
Proof. move=> hx hy. radcan. all: by rewrite ?exprn_ge0. Qed.

Lemma f7 : 0 <= x -> 0 <= y ->
  \sqrt (\sqrt (x / y)) = \sqrt (\sqrt x) / \sqrt (\sqrt y).
Proof. move=> hx hy. radcan. all: by rewrite ?proot_ge0. Qed.

(* constant fractions are left to plain radcan, unchanged *)
Lemma f8 : \sqrt (2 / 3) = \sqrt 6 / 3.
Proof. by radcan. Qed.
End Generic.

Section Real.
Variables (R : rcfType) (x y : R).

(* real mode: odd roots split with no condition from frac_split *)
Lemma g1 : rootR 3 (x / 8) = rootR 3 x / 2.
Proof. by radcan. Qed.

(* 0 <= y comes from the checker (the inverse of rootR 3 y), not from     *)
(* frac_split                                                              *)
Lemma g2 : 0 <= y -> rootR 3 (x / y) = rootR 3 x / rootR 3 y.
Proof. move=> h. radcan. exact: h. Qed.

(* refined: 1 <= x *)
Lemma g3 : 1 <= x ->
  rootR 2 ((x - 1) / (x + 2)) = rootR 2 (x - 1) / rootR 2 (x + 2).
Proof. move=> h. radcan. exact: h. Qed.
End Real.

Section Complex.
Variables (C : numClosedFieldType) (x : C).

(* refined: -1 <= x *)
Lemma h1 : -1 <= x -> 2.-root ((x + 1) / 4) = 2.-root (x + 1) / 2.
Proof. move=> h. radcan. exact: h. Qed.
End Complex.
```

## Part 27 — explicit values of small roots of unity (milestone Ω1)

mathcomp's `n.-root (−1)` is the root of `Xⁿ + 1` in the upper half-plane
with the largest real part, i.e. `ω_n = e^{iπ/n}`. `OmegaC.v` proves this
characterisation (`rootC_char`, `sqrtC_char`), the index law for `k = 2`
(`rootC_double : (2n).-root x = sqrtC (n.-root x)`) and the values

- `ω₃ = (1 + √3·i)/2`, `ω₄ = (√2/2)(1 + i)`, `ω₆ = (√3 + i)/2`,
- `ω₁₂ = ((√6+√2) + (√6−√2)·i)/4`,

packaged as the record `smallroot` (`OmegaRoot.v`) with the instance
`rootC_smallroot C`.

```coq
Section Omega.
Variable C : numClosedFieldType.

(* the explicit values, in Q(i, sqrt 2, sqrt 3) *)
Check omega1C C : 1.-root (-1 : C) = -1.
Check omega2C C : 2.-root (-1 : C) = 'i.
Check omega3C C : 3.-root (-1 : C) = (1 + sqrtC 3 * 'i) / 2.
Check omega4C C : 4.-root (-1 : C) = sqrtC 2 / 2 * (1 + 'i).
Check omega6C C : 6.-root (-1 : C) = (sqrtC 3 + 'i) / 2.
Check omega12C C : 12.-root (-1 : C) =
  ((sqrtC 6 + sqrtC 2) + (sqrtC 6 - sqrtC 2) * 'i) / 4.

(* the characterisation used to prove them *)
Check @rootC_char C.
Check @rootC_double C.

(* cyclotomic and index relations, proved in OmegaC.v *)
Check omega3_cycloC C : 3.-root (-1 : C) ^+ 2 - 3.-root (-1) + 1 = 0.
Check omega4_sqrC C : 4.-root (-1 : C) ^+ 2 = 2.-root (-1).
Check omega4_sqrt2C C : 4.-root (-1 : C) - 4.-root (-1) ^+ 3 = sqrtC 2.
Check omega4_invC C : 4.-root (-1 : C) + (4.-root (-1))^-1 = sqrtC 2.
Check omega6_sqrC C : 6.-root (-1 : C) ^+ 2 = 3.-root (-1).
Check omega6_cubeC C : 6.-root (-1 : C) ^+ 3 = 'i.
Check omega12_sqrC C : 12.-root (-1 : C) ^+ 2 = 6.-root (-1).
Check omega12_cubeC C : 12.-root (-1 : C) ^+ 3 = 4.-root (-1).

(* radcan alone does not see these relations (Tutorial 16); after
   unfolding the explicit values (and 'i back into 2.-root (-1)) it does *)
Lemma o1 : 3.-root (-1 : C) ^+ 2 - 3.-root (-1) + 1 = 0.
Proof. by rewrite omega3C -omega2C; radcan. Qed.

Lemma o2 : 4.-root (-1 : C) ^+ 2 = 2.-root (-1).
Proof. by rewrite omega4C -omega2C; radcan. Qed.

Lemma o3 : 12.-root (-1 : C) ^+ 3 = 4.-root (-1).
Proof. by rewrite omega12C omega4C -omega2C; radcan. Qed.

(* paper eq. (2), second reading *)
Lemma o4 : (4.-root (-1 : C))^-1 - (4.-root (-1))^-1 ^+ 3 - sqrtC 2 = 0.
Proof. by rewrite omega4C -omega2C; radcan. Qed.

End Omega.

(* the record, with its instance on C *)
Check @smallroot.
Check fun C : numClosedFieldType => rootC_smallroot C.
```

## Part 28 — using the values of ω (milestone Ω2)

`omega_rw` (`OmegaPass.v`) replaces `3.-root(−1)`, `4.-root(−1)`,
`6.-root(−1)` and `12.-root(−1)` by their values, and a root of a negative
constant `n.-root(−c)` by `n.-root c · ω_n`. The neg checker then works with
`ω₂ = √(−1)` only, reduced by `ω₂² = −1`. This proves the two goals that
Part 16 had to leave out (`ω₃² − ω₃ + 1 = 0`, `ω₄² = ω₂`) and the paper's
(2) in its second reading.

```coq
(* radcan_with_gen of Tactic.v in neg mode, with omega_rw before the checker *)
Ltac radcan_omega_with_gen refined r w ov :=
  radcan_reify r;
  lazymatch goal with
  | |- rinterp _ ?env ?e1 = rinterp _ _ ?e2 =>
      let p1 := eval vm_compute in (omega_rw e1) in
      let p2 := eval vm_compute in (omega_rw e2) in
      lazymatch p1 with (?f1, ?cs1) =>
      lazymatch p2 with (?f2, ?cs2) =>
      let c := eval vm_compute in (radcan_check_neg f1 f2) in
      lazymatch c with
      | Some ?cs =>
          lazymatch refined with
          | true =>
              let rcs := eval vm_compute in (refine (cs1 ++ cs2 ++ cs)) in
              apply: (@radcan_eq_omega_refined _ r w env ov
                        e1 e2 f1 f2 cs1 cs2 cs rcs);
              [vm_compute; reflexivity | vm_compute; reflexivity
              | vm_compute; reflexivity | vm_compute; reflexivity
              | radcan_split_rconds]
          | false =>
              apply: (@radcan_eq_omega _ r w env ov
                        e1 e2 f1 f2 cs1 cs2 cs);
              [vm_compute; reflexivity | vm_compute; reflexivity
              | vm_compute; reflexivity | radcan_split_conds]
          end
      | None => fail "radcan_omega: the normal forms differ"
      end end end
  end.

(* the dispatch: a proot r goal with ov : smallroot w (w : negroot r), or  *)
(* an n.-root goal on C (rootC_negroot C, rootC_smallroot C of OmegaC.v)    *)
Ltac radcan_omega_only refined :=
  lazymatch goal with
  | |- context [proot ?r _ _] =>
      lazymatch goal with
      | ov : @smallroot _ r ?w |- _ => radcan_omega_with_gen refined r w ov
      end
  | |- context [@nthroot ?C _ _] =>
      radcan_omega_with_gen refined (rootC_posroot C) (rootC_negroot C)
        (rootC_smallroot C)
  end.

(* plain radcan first, so that the goals it proves keep their conditions *)
Ltac radcan_omega_gen refined :=
  first [radcan_gen refined | radcan_omega_only refined].

Ltac radcan_omega := radcan_omega_gen true.
Ltac radcan_omega_raw := radcan_omega_gen false.

Section Generic.
Variables (F : numFieldType) (r : posroot F) (w : negroot r).
Hypothesis ov : smallroot w.
Variable x : F.
Local Notation "\w_ n" := (proot r n (-1)) (at level 3, n at level 2).

Lemma o1 : \w_3 ^+ 2 - \w_3 + 1 = 0.
Proof. Fail radcan. radcan_omega. Qed.

(* the index law, through the explicit values *)
Lemma o2 : \w_4 ^+ 2 = \w_2.
Proof. Fail radcan. radcan_omega. Qed.

Lemma o3 : \w_6 ^+ 2 = \w_3.
Proof. Fail radcan. radcan_omega. Qed.

Lemma o4 : \w_12 ^+ 3 = \w_4.
Proof. Fail radcan. radcan_omega. Qed.

Lemma o5 : \w_6 ^+ 3 = \w_2.
Proof. Fail radcan. radcan_omega. Qed.

Lemma o6 : \w_12 ^+ 2 = \w_6.
Proof. radcan_omega. Qed.

(* omega_4 + omega_4 ^-1 = sqrt 2 *)
Lemma o7 : \w_4 + (\w_4)^-1 = proot r 2 2.
Proof. Fail radcan. radcan_omega. Qed.

(* negative constant radicands: n.-root (- p / d) = n.-root (p / d) omega_n *)
Lemma o8 : proot r 3 (-8) = 1 + proot r 2 3 * \w_2.
Proof. Fail radcan. radcan_omega. Qed.

Lemma o9 : proot r 4 (- (1 / 4)) = (1 + \w_2) / 2.
Proof. Fail radcan. radcan_omega. Qed.

Lemma o10 : proot r 12 (-1) ^+ 4 = proot r 3 (-1).
Proof. radcan_omega. Qed.

(* the paper's (2), second reading ((1 - x)^(3/4) = ((1 - x)^(1/4))^3):     *)
(* 4.-root (1 - x) = 4.-root (x - 1) * omega_4 under 0 <= x - 1, so the     *)
(* left side is omega_4^-1 - omega_4^-3 - sqrt 2 = 0                        *)
(* raw: 0 <= - (1 - x) (omega_rw, twice), 0 <= x - 1, x - 1 != 0           *)
(* refined: 1 < x                                                           *)
Lemma paper2 : 1 < x ->
  proot r 4 (x - 1) / proot r 4 (1 - x)
  - proot r 4 (x - 1) ^+ 3 / proot r 4 (1 - x) ^+ 3 - proot r 2 2 = 0.
Proof. move=> h. Fail radcan. radcan_omega. exact: h. Qed.

(* first reading ((1 - x)^(3/4) = 4.-root ((1 - x)^3)): the principal roots *)
(* make the first two terms cancel, so the left side of (2) is - sqrt 2;   *)
(* plain radcan already proves it (the omega_4 atoms cancel)               *)
Lemma paper2' : 1 < x ->
  proot r 4 (x - 1) / proot r 4 (1 - x)
  - proot r 4 ((x - 1) ^+ 3) / proot r 4 ((1 - x) ^+ 3) = 0.
Proof. move=> h. radcan. exact: h. Qed.
End Generic.

(* On C: n.-root goals, with rootC_negroot C and rootC_smallroot C (OmegaC.v) *)
Section Complex.
Variables (C : numClosedFieldType) (x : C).

(* the two Fail goals of TUTORIAL Part 16 *)
Lemma c1 : 3.-root (-1 : C) ^+ 2 - 3.-root (-1) + 1 = 0.
Proof. Fail radcan. radcan_omega. Qed.

Lemma c2 : 4.-root (-1 : C) ^+ 2 = 2.-root (-1).
Proof. Fail radcan. radcan_omega. Qed.

Lemma c3 : 6.-root (-1 : C) ^+ 2 = 3.-root (-1).
Proof. Fail radcan. radcan_omega. Qed.

Lemma c4 : 12.-root (-1 : C) ^+ 3 = 4.-root (-1).
Proof. Fail radcan. radcan_omega. Qed.

(* the principal cube root of -8 *)
Lemma c5 : 3.-root (-8 : C) = 1 + 2.-root 3 * 2.-root (-1).
Proof. Fail radcan. radcan_omega. Qed.

(* paper (2), second reading; refined: 1 < x *)
Lemma c6 : 1 < x ->
  4.-root (x - 1) / 4.-root (1 - x)
  - 4.-root (x - 1) ^+ 3 / 4.-root (1 - x) ^+ 3 - 2.-root 2 = 0.
Proof. move=> h. Fail radcan. radcan_omega. exact: h. Qed.
End Complex.
```

## Part 29 — the composed pre-pass (`Prepass.v`)

When the plain check fails, `radcan` rewrites both sides with a composed
pre-pass and checks again. Each round applies

1. `omega_rw` (only on ℂ, or with a `smallroot` in the context): values of
   small roots of unity, `n.-root(−c) = n.-root c · ω_n`;
2. `frac_split`: roots of fractions;
3. `denest_rwc`: denesting (constants, variables, several roots);

and rounds are repeated until nothing changes (at most `radcan_fuel = 4`).
Every pass comes with a soundness lemma and the conditions it needs; the
decision theorems `radcan_eq_pre*` chain them with the usual checker. Goals
the plain check proves are not affected.

```coq
Section Generic.
Variables (F : numFieldType) (r : posroot F) (x : F).
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).

(* fractions, then denesting of sqrt (3 + 2 sqrt 2)                         *)
(* refined: 0 <= x (the checker, 1 / sqrt x); 0 <= 3 + 2 sqrt 2 from       *)
(* frac_split is dropped (sign certificate, SignCert.v)                    *)
Lemma p1 : 0 <= x -> \sqrt ((3 + 2 * \sqrt 2) / x) = (1 + \sqrt 2) / \sqrt x.
Proof.
move=> h. Fail radcan_plain_gen true. radcan; exact: h.
Qed.

(* fractions, then denesting with a variable                               *)
(* refined: 1 <= x; 0 <= x + 2 sqrt (x - 1) (frac_split) follows from it    *)
Lemma p2 : 1 <= x ->
  \sqrt ((x + 2 * \sqrt (x - 1)) / 4) = (1 + \sqrt (x - 1)) / 2.
Proof.
move=> h. radcan; exact: h.
Qed.

(* denesting creates fractions: sqrt (x + sqrt (x^2 - 4)) is              *)
(* sqrt ((x + 2) / 2) + sqrt ((x - 2) / 2), split at the second round      *)
Lemma p3 : 2 <= x ->
  \sqrt (x + \sqrt (x ^+ 2 - 4)) * \sqrt 2 = \sqrt (x + 2) + \sqrt (x - 2).
Proof. move=> h. radcan. exact: h. Qed.

(* a constant fraction: sqrt (3 / 2 + sqrt 2) = 1 + sqrt 2 / 2 *)
Lemma p4 : \sqrt (3 / 2 + \sqrt 2) * \sqrt 2 = \sqrt 2 + 1.
Proof. Fail radcan_plain_gen true. by radcan. Qed.

(* the pre-pass alone: (sqrt (3 + 2 sqrt 2) * sqrt x ^-1) denested *)
Eval vm_compute in
  prepass false false 4
    (RRootE 2 (RMul (RAdd (RCst 3) (RMul (RCst 2) (RRoot 2 2)))
                    (RInv (RVar 0)))).
End Generic.

(* omega_rw runs first (with a smallroot): n.-root (-8 / x) becomes        *)
(* n.-root (8 / x) * omega_n, then frac_split splits 8 / x                   *)
Section Omega.
Variables (F : numFieldType) (r : posroot F) (w : negroot r) (x : F).
Hypothesis ov : smallroot w.

(* refined: 0 <= x (0 <= x^-1 is read as 0 <= x) *)
Lemma o1 : 0 < x ->
  proot r 3 (-8 / x) = (1 + proot r 2 3 * proot r 2 (-1)) / proot r 3 x.
Proof. move=> h. radcan. all: by rewrite ?invr_ge0 ltW. Qed.
End Omega.

Section Complex.
Variables (C : numClosedFieldType) (x : C).

Lemma c1 : 0 < x ->
  3.-root (-8 / x) = (1 + 2.-root 3 * 2.-root (-1)) / 3.-root x.
Proof. move=> h. radcan. all: by rewrite ?invr_ge0 ltW. Qed.
End Complex.

(* Limitation: omega_rw does not see the sign of a fraction radicand with  *)
(* a variable, so 4.-root ((1 - x) / y) is first split by frac_split under *)
(* 0 <= 1 - x, then 4.-root (1 - x) rewritten under 0 <= x - 1: the goal  *)
(* is proved only for x = 1                                                *)
```

## Part 30 — roots given by hypotheses (`Sym.v`, `SymTac.v`, milestone M15)

Script: [`tutorial/Tut30_sym.v`](tutorial/Tut30_sym.v).

The paper (§3) reads a radical as a formal generator of a field extension:
(x−1)^(1/2) is *some* y with y² = x − 1, not a branch of a root function.
`radcan_sym` works in that reading. The user introduces his own symbols with
defining equations, `hy : y ^+ n = B` or `hz : z = B` (y an atom, n a
literal > 0, B any expression), and the goal is proved for **every** choice
of the symbols:

```coq
Hypotheses (hy : y ^+ 2 = x - 1) (hz : z ^+ 4 = 1 - x) (hw : w ^+ 4 = -1).
Lemma sym1 : y ^+ 3 = (x - 1) * y.           Proof. radcan_sym. Qed.
Lemma sym3 : z ^+ 4 + y ^+ 2 = 0.            Proof. radcan_sym. Qed.
Lemma sym4 : y^-1 = y / (x - 1).             Proof. radcan_sym. Qed.
Lemma sym6 : (w - w ^+ 3) ^+ 2 = 2.          Proof. radcan_sym. Qed.
```

In the normaliser (`Sym.v`) a symbol is a variable, reduced only by
y^k → B^(k / n) y^(k mod n) and y⁻¹ → y^(n−1) B⁻¹ (true in any field, even
for y = 0). There is no multiplicativity, merging, sign law or branch, so no
side condition except the cancellations B ≠ 0 of a division. Two symbols with
the same relation stay different (`v = y` is refused, `(v - y) (v + y) = 0`
is proved). The theorem is

```coq
radcan_eq_cond_sym : radcan_check_sym rels e1 e2 = Some cs ->
  rels_hold rt env rels -> all_conds_gen rt env cs ->
  rinterp_gen rt env e1 = rinterp_gen rt env e2      (* any rt *)
```

`rels_hold` asks only for the relations, `nth 0 env i ^+ n = B`. The tactic
proves it from the hypotheses.

**The paper's (2), in its own reading.** u = (x−1)^(1/4), w = (−1)^(1/4),
(1−x)^(1/4) = w u, and √2 is the element w − w³ of the extension:

```coq
Hypotheses (hu : u ^+ 4 = x - 1) (hw : w ^+ 4 = -1) (hz : z = w * u).
Lemma paper2 : x != 1 -> u / z - u ^+ 3 / z ^+ 3 - (w - w ^+ 3) = 0.
Proof. move=> h. radcan_sym. by rewrite subr_eq0. Qed.
```

The cancellation u / u leaves the condition `x - 1 != 0`. The paper leaves
it implicit, but at x = 1 the left side is −√2. Without `z = w * u` (z any
fourth root of 1 − x), the goal is refused.

Limitations: inverses of sums with symbols are rationalised since Part 32; the reduction is not a
Gröbner basis, so relations whose right sides contain other symbols can miss
identities; every equation `a = B` with an atom `a` in the context is used as
a rule.

## Part 31 — roots of unity under fractions

`omega_rw` now looks inside a fraction `P/Q` and tests the signs of `P` and
`Q` separately: `n.-root(−P/Q) = n.-root(P/Q) · ω_n` (and the same for a
negative denominator), with the same conditions as `frac_split` produces
afterwards, so the two passes agree. `4.-root((1−x)/y)` gives `1 <= x`,
`0 <= y` instead of the contradictory `1 <= x`, `x <= 1`.

```coq
Section Complex.
Variables (C : numClosedFieldType) (x y : C).

(* numerator negative; refined: 1 <= x, 0 <= y *)
Lemma c1 : 1 <= x -> 0 < y ->
  4.-root ((1 - x) / y) = 4.-root (x - 1) / 4.-root y * 4.-root (-1).
Proof. move=> hx hy. radcan; [exact: hx | exact: ltW]. Qed.

(* a negative constant numerator, n = 2; refined: 0 <= x *)
Lemma c2 : 0 < x -> 2.-root (-4 / x) = 2 * 2.-root (-1) / 2.-root x.
Proof. move=> h. radcan. exact: ltW. Qed.

(* the cube root of Tutorial 29 (omega_3 explicit); refined: 0 <= x *)
Lemma c3 : 0 < x ->
  3.-root (-8 / x) = (1 + 2.-root 3 * 2.-root (-1)) / 3.-root x.
Proof. move=> h. radcan. exact: ltW. Qed.

(* denominator negative; refined: 0 <= x, 1 <= y *)
Lemma c4 : 0 <= x -> 1 <= y ->
  4.-root (x / (1 - y)) = 4.-root x / 4.-root (y - 1) * 4.-root (-1).
Proof. move=> hx hy. radcan; [exact: hx | exact: hy]. Qed.

(* both negative: no omega_n; refined: 0 <= x, 1 <= y *)
Lemma c5 : 0 <= x -> 1 < y ->
  2.-root (- x / (1 - y)) = 2.-root x / 2.-root (y - 1).
Proof. move=> hx hy. radcan; [exact: hx | exact: ltW]. Qed.

(* a constant denominator; refined: 1 <= x *)
Lemma c6 : 1 <= x ->
  3.-root ((1 - x) / 8) = 3.-root (x - 1) / 2 * 3.-root (-1).
Proof. move=> h. radcan. exact: h. Qed.
End Complex.

Section Generic.
Variables (F : numFieldType) (r : posroot F) (w : negroot r) (x y : F).
Hypothesis ov : smallroot w.

(* refined: 1 <= x, 0 <= y *)
Lemma g1 : 1 <= x -> 0 < y ->
  proot r 4 ((1 - x) / y) = proot r 4 (x - 1) / proot r 4 y * proot r 4 (-1).
Proof. move=> hx hy. radcan; [exact: hx | exact: ltW]. Qed.

(* refined: 0 <= x *)
Lemma g2 : 0 < x -> proot r 2 (-4 / x) = 2 * proot r 2 (-1) / proot r 2 x.
Proof. move=> h. radcan. exact: ltW. Qed.

(* the radicand is -1 for x <> 1: the denominator is flipped, then         *)
(* 4.-root (x - 1) / 4.-root (x - 1) cancels; refined: x != 1 (1 <= x)    *)
Lemma g3 : 1 < x -> proot r 4 ((x - 1) / (1 - x)) = proot r 4 (-1).
Proof. by move=> h; radcan; rewrite gt_eqF. Qed.
End Generic.
```

## Part 32 — inverses with symbols (milestone M21)

The paper computes in a field extension such as `ℚ(x)[y]` with `y² = x − 1`
and inverts any element. `radcan_sym` now does the same: an inverse `1/d`
where `d` mixes symbols is replaced by `u / E` with `E` free of symbols, `u`
found by fraction-free elimination on the basis `yᵏ` (`k < n`), and only the
product `d · u = E` checked. The new condition is `E != 0`. As with real
roots (Part 18), this is a fallback: goals proved before keep their
conditions.

```coq
(* y = (x - 1)^(1/2): (1 + y) (y - 1) = y^2 - 1 = x - 2 *)
Section Sqrt.
Variables (F : numFieldType) (x y : F).
Hypothesis hy : y ^+ 2 = x - 1.

(* condition: x - 2 != 0 *)
Lemma syminv1 : x != 2 -> 1 / (1 + y) = (y - 1) / (x - 2).
Proof. move=> h. radcan_sym. by rewrite subr_eq0. Qed.

Lemma syminv2 : x != 2 -> 1 / (y + 1) + 1 / (y - 1) = 2 * y / (x - 2).
Proof. move=> h. radcan_sym. by rewrite subr_eq0. Qed.

Lemma syminv3 : x != 2 -> (x - 1) / (1 + y) = (x - 1) * (y - 1) / (x - 2).
Proof. move=> h. radcan_sym. by rewrite subr_eq0. Qed.

(* the plain check is tried first: no rationalisation, no x != 2 *)
Lemma syminv4 : y + 1 != 0 -> (1 + y) / (1 + y) = 1.
Proof. move=> h. radcan_sym. exact: h. Qed.
End Sqrt.

(* s = (x + 1)^(1/3): (1 + s) (1 - s + s^2) = 1 + s^3 = x + 2 *)
Section Cbrt.
Variables (F : numFieldType) (x s : F).
Hypothesis hs : s ^+ 3 = x + 1.

Lemma syminv5 : x != -2 -> 1 / (1 + s) = (1 - s + s ^+ 2) / (x + 2).
Proof. move=> h. radcan_sym. by rewrite addr_eq0. Qed.
End Cbrt.

(* two symbols: (y + z) (z - y) = z^2 - y^2 = 1, no condition at all *)
Section Two.
Variables (F : numFieldType) (x y z : F).
Hypotheses (hy : y ^+ 2 = x) (hz : z ^+ 2 = x + 1).

Lemma syminv6 : 1 / (y + z) = z - y.
Proof. radcan_sym. Qed.
End Two.

(* the paper's style: x + y + w, w = (-1)^(1/4), y = (x - 1)^(1/2); the     *)
(* basis has 8 monomials and E (the norm of x + y + w over Q(x)) degree 8;  *)
(* about 2.5 s for the tactic and 1 s for Qed                               *)
Section Stress.
Variables (F : numFieldType) (x y w : F).
Hypotheses (hy : y ^+ 2 = x - 1) (hw : w ^+ 4 = -1).

Lemma syminv7 : x ^+ 4 + 1 != 0 -> 1 / (x + w) =
  (x ^+ 3 - x ^+ 2 * w + x * w ^+ 2 - w ^+ 3) / (x ^+ 4 + 1).
Proof. move=> h. radcan_sym. exact: h. Qed.

Lemma syminv8 : x != 2 ->
  x ^+ 8 - 4 * x ^+ 7 + 10 * x ^+ 6 - 16 * x ^+ 5 + 21 * x ^+ 4
    - 4 * x ^+ 3 - 8 * x + 4 != 0 ->
  (x + y + w) * (1 / (x + y + w) + 1 / (1 + y)) =
  1 + (x + y + w) * (y - 1) / (x - 2).
Proof.
move=> h2 h. radcan_sym; first by rewrite subr_eq0.
(* E != 0, E printed in the normaliser's order *)
by move: h; apply: contra_neq => <-; radcan_sym.
Qed.
End Stress.
```

## Part 33 — roots of unity of different indices, and three square roots

Script: [`tutorial/Tut33_omega_merge.v`](tutorial/Tut33_omega_merge.v).

On ℂ, `ω_n = n.-root (-1)` is the principal `n`-th root of `−1`, i.e.
`e^{iπ/n}`. Until now each `ω_n` was a separate atom, reduced only by
`ω_n ^+ n = -1`, so `ω_4 ^+ 2` and `ω_2` were different normal forms. Two
facts about mathcomp's principal roots, proved in `UnitArc.v` without any
trigonometry, change that:

```coq
Lemma rootC_N1_index n k : (0 < n)%N -> (0 < k)%N ->
  (n * k).-root (-1 : C) ^+ k = n.-root (-1).
Lemma rootC_N1_prim n : (0 < n)%N ->
  (2 * n).-primitive_root (n.-root (-1 : C)).
```

With the index law (record `cycroot w`, `OmegaRoot2.v`) the normaliser merges
the `ω` atoms of a monomial over the lcm of their indices, as Part 11 merges
`√[n]B` and `√[m]B`:

```coq
Goal 10.-root (-1 : C) ^+ 2 = 5.-root (-1). Proof. radcan. Qed.
Goal 8.-root (-1 : C) ^+ 2 * 5.-root (-1) = 20.-root (-1) ^+ 9.
Proof. radcan. Qed.
```

The same file has a deliberately small table (record `sqrtroot w`): when the
goal contains `ω_4`, `ω_6` or `ω_5`, the constant square roots of 2, 3 and 5
are written with roots of unity,

  `√2 = ω₄ − ω₄³`, `√3 = ω₆ − ω₆⁵`, `√5 = 2ω₅ − 2ω₅⁴ − 1`,

so that, for example, the golden ratio is recognised:

```coq
Goal 10.-root (-1 : C) ^+ 2 + (5.-root (-1))^-1 = (2.-root 5 + 1) / 2.
Proof. radcan. Qed.
```

This table is a recipe, not a general method. In general `√p` is a Gauss
sum of `p`-th roots of unity, but with principal roots its sign is Gauss's
sign theorem, which we do not prove. Only 2, 3, 5 are covered.

## Part 34 — cyclotomic reduction

Script: [`tutorial/Tut34_cyclo.v`](tutorial/Tut34_cyclo.v).

After Part 33 every monomial carries at most one `ω_n ^+ k`, but sums can
still be zero without being recognised: `ω_5` is a root of the cyclotomic
polynomial `Φ₁₀ = X⁴ − X³ + X² − X + 1`. `Cyclo.v` writes every `ω_n ^+ k`
as a power of `ω_N`, `N` the lcm of the indices of both sides, and reduces
modulo `Φ_{2N}`. The polynomial `Φ_{2N}` is computed over ℤ without proof
and then checked by a certificate:

```coq
Lemma prim_root_cert (R : idomainType) m (z : R) (p h g : {poly R}) D :
  m.-primitive_root z -> all (fun d => (0 < d < m)%N) D ->
  p * h = 'X^m - 1 -> h * g = \prod_(d <- D) ('X^d - 1) -> root p z.
```

Soundness needs that `ω_N` is a primitive `2N`-th root of unity (record
`cycprim w`, instance from `rootC_N1_prim`).

```coq
Goal 5.-root (-1 : C) ^+ 4 - 5.-root (-1) ^+ 3 + 5.-root (-1) ^+ 2
  - 5.-root (-1) + 1 = 0.
Proof. radcan. Qed.
```

A false identity such as `ω₇³ + ω₇ = ω₇²` is refused. An `ω` inside the
inverse of a sum, as in `(1 + ω₅)⁻¹`, is still an opaque atom.

## Part 35 — a trigonometric identity through ℂ

Script: [`tutorial/Tut35_imo1963.v`](tutorial/Tut35_imo1963.v). It needs the
package `rocq-mathcomp-real-closed` for ℂ = `R[i]`.

IMO 1963, problem 5, on the reals of the standard library:

```coq
Theorem imo1963 : cos (PI / 7) - cos (2 * PI / 7) + cos (3 * PI / 7) = 1 / 2.
```

`radcan` knows nothing about `cos`. The idea is to go to ℂ, where the
identity becomes algebra:

1. `E x := cos x +i* sin x` in `R[i]`. With the addition formulas,
   `E x * E y = E (x + y)` (`EM`); the complex product is checked by
   `radcan_sym`, with `i` a symbol such that `i ^+ 2 = -1`.
2. De Moivre by induction: `E x ^+ n = E (INR n * x)` (`EX`).
3. For `z := E (PI / 7)`: `z ^+ 7 = -1` (`z7`), and `z + 1 != 0` because
   `sin (PI / 7) > 0`. So `z` is a root of
   `Φ₁₄ = (X⁷ + 1) / (X + 1)` (`Phi14`): `radcan_sym` proves
   `(z + 1) * Φ₁₄(z) = 0` from `z ^+ 7 = -1`.
4. `2 cos (k t) = E (k t) + E (- k t)` and `E (- k t) = - z ^+ (7 - k)`.
   The identity, times 2, becomes `z - z² + z³ - z⁴ + z⁵ - z⁶ = 1`,
   proved by `radcan_sym` from `Φ₁₄(z) = 0` (`mainC`).
5. Back to ℝ by taking real parts, then `lra`.

In this first proof the roots of unity of Parts 16 and 33–34 are not used:
`z` is a symbol with a relation, as in Part 30.

A second proof (`imo1963_omega`) uses them. `z_root` shows that `z` *is*
mathcomp's principal root `7.-root (-1)`: `z` is a primitive 14-th root of
unity, so `7.-root (-1) = z ^+ j`; `'Im ≥ 0` excludes `j = 8…13` (`sin < 0`
on `]π, 2π[`), and `rootC_N1_max` (largest real part) excludes `j = 2…7`
(`cos` decreasing on `[0, π]`). Then plain `radcan` proves the identity in
`ω₇`, with the cyclotomic reduction of Part 34:

```coq
Proof. rewrite !Ezk !Enk //= z_root. radcan. Qed.
``` The theorem uses the axioms of the
standard reals and `epsilon_statement` (from `Rstruct.v`).

## The paper's examples (`paper/Paper.v`)

`paper/Paper.v` runs the examples of Caviness and Fateman through `radcan`.

| Paper | Result |
|---|---|
| §2: `(2^{1/6})^7 = 2·2^{1/6}` | proved |
| §2 form 2: `√(x⁴+9x³+29x²+39x+18) = (x+3)√(x²+3x+2)` | proved, conditions `-3 <= x`, `-2 <= 3x + x²` |
| §2: the same plus `∛(x+2)`, over index 6 | proved, condition `-1 <= x` |
| (1) as an identity `x − y = (√x−√y)(√x+√y)` | proved, conditions `0 <= x`, `0 <= y` |
| (8): `(x+√2+∛9)·N = (x+√2)³+9` | proved |
| end of §2: `D · conj(D) = E` | proved with `108 x`; the printed `54 x` is **refused** |
| (3) as printed | **refused: it is false** (check at `x = 5/2`) |
| (1) as a quotient `(x−y)/(√x+√y) = √x−√y` | proved (M11), conditions `0 <= x`, `0 <= y`, `x != y` |
| (3) as a quotient, with the corrected `E` | proved (M11), condition `E != 0` |
| (2) | first reading (`n.-root` of powers): false on ℂ, the left side is `−√2` (proved); second reading (powers of roots): proved under `1 < x` with the values of `ω₄` (Part 28); the paper's own symbolic reading (roots given by hypotheses): proved by `radcan_sym` under `x != 1` (Part 30) |
| (4) = (6) on ℂ, with `ω = 3.-root(−1)` | proved (M13), condition `-1 <= x²`; with a 6th root of `−1` it is false and refused |
| §2 nested example `√(x²+3x+3+√(x+1)√(x+1)) = x+2` | proved (M13), condition `-1 <= x` |

So `radcan` found two misprints in the paper: in (3) and in the coefficient
of `x` in `E`.

## The files

| File | Content |
|---|---|
| `PosRoot.v`, `PosRootFacts.v` | root interfaces `posroot`, `oddroot`, `negroot` and their lemmas |
| `RootC.v`, `RootR.v` | instances for ℂ (`n.-root`) and real closed fields (`rootR`) |
| `OmegaRoot.v`, `OmegaC.v` | explicit small roots of unity (`smallroot`, `rootC_smallroot`) |
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
| `OmegaRoot2.v`, `NegCyc.v`, `CycC.v` | records `cycroot` (index law) and `sqrtroot` (√2, √3, √5 table), their theorems and ℂ instances |
| `Cyclo.v`, `CycloC.v`, `CycloTac.v` | cyclotomic reduction: certified `Φ`, record `cycprim`, ℂ instance, `radcan_cyc` |
| `Tactic.v` | reification and the tactics `radcan`, `radcan_raw` |
| `Sym.v`, `SymTac.v` | roots given by hypotheses (y ^+ n = B), `radcan_sym` |
| `Simplify.v`, `SimplifyTac.v` | printing normal forms back; `radcan_simplify` |
| `Examples.v`, `RefineEx.v` | examples with timings |

## What does not work yet

- The composed pre-pass is slow on denesting with variables (about 4 s per goal).
- Conditions on constants are dropped only when they hold whether the roots
  are read as their true value or as 0 (the root-free theorem
  `radcan_eq_refined0` shares `refine`): `0 <= 3 - 2 * sqrt 2` and
  `1 + sqrt 2 != 0` disappear, `sqrt 2 != 0` and `0 <= sqrt 2 - 1` stay.

- `radcan_simplify` shows whatever normal form the normaliser chose: constant
  radicands stay split over the basis, rational constants are not put over a
  common denominator, numerals above 100000 show as `(Pos.to_nat p)%:R`; on
  Stdlib reals the result is in mathcomp notation (`rootR`, `` `|x|``).

- Rationalisation (Part 18) is all-or-nothing on a goal and adds the condition `E ≠ 0`,
  which can be a large polynomial.

- Refinement combines conditions only when they are linear in their monomials (`x*y`,
  `x^2` are independent unknowns).
- Absolute values only on real fields with roots (`rootR`, or a `realroot`): on a general
  `numFieldType`, `√((x−2)²) = x − 2` needs `2 <= x`.
- `√(1−x)·√(x−1) = 0` is not proved (it needs `x = 1`).
- Even roots of negatives (`√(−4)`) stay opaque on ℝ. On ℂ they use `ω_n`, merged across
  indices and reduced modulo cyclotomic polynomials, but an `ω` inside the inverse of a
  sum or inside a radicand stays an opaque atom.
- Square roots are written with roots of unity only for 2, 3 and 5 (Part 33).
