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

- duplicates and conditions that are true on constants (`0 <= 3`) disappear;
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
(* radcan leaves:  0 <= x   and   0 <= sqrt x  (printed rootR 2 x) *)
- by radcan_Rstd_back; lra.
- by rewrite -sqrtE; apply/RleP/sqrt_pos.
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

(* omega_3 is a root of x^2 - x + 1 is NOT found: omega atoms are only      *)
(* reduced by omega_n ^+ n = -1 (no cyclotomic relation)                    *)
Goal 3.-root (-1 : C) ^+ 2 - 3.-root (-1) + 1 = 0.
Proof. Fail radcan. Abort.

(* omega atoms of different indices are not merged (no index law) *)
Goal 4.-root (-1 : C) ^+ 2 = 2.-root (-1).
Proof. Fail radcan. Abort.

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
| (2) on ℂ | not proved: with principal roots it is false (`−√2`); the paper's convention needs the cyclotomic relation of `ω₈` |
| (4) = (6) on ℂ, with `ω = 3.-root(−1)` | proved (M13), condition `-1 <= x²`; with a 6th root of `−1` it is false and refused |
| §2 nested example `√(x²+3x+3+√(x+1)√(x+1)) = x+2` | proved (M13), condition `-1 <= x` |

So `radcan` found two misprints in the paper: in (3) and in the coefficient
of `x` in `E`.

## The files

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
| `IrrFactor.v`, `MFactor.v`, `MFactorEEZ.v` | polynomial factoring over ℤ: one variable (Berlekamp–Hensel–Zassenhaus), several variables (homogeneous, linear factors, Wang's EEZ) |
| `Poly.v` | polynomial exact division, gcd, square-free factoring, radicand basis |
| `Ratio.v` | rationalisation of denominators with variables and roots |
| `Inverse.v` | inverse by linear algebra, checked |
| `Cond.v` | radicands, cancellation, conditions, modes, `radcan_check` and soundness |
| `Radcan.v`, `RadcanBig.v` | the two instances of the normaliser |
| `RefPoly.v`, `RefCheck.v`, `RefHeur.v`, `Refine.v` | refinement of the conditions: polynomials over atoms, proved checker, unverified heuristics, `refine` and its soundness |
| `OddRoot.v`, `NegRootC.v`, `AbsRoot.v` | theorems for odd roots (ℝ), roots of unity (ℂ), real fields |
| `Tactic.v` | reification and the tactics `radcan`, `radcan_raw` |
| `Simplify.v`, `SimplifyTac.v` | printing normal forms back; `radcan_simplify` |
| `Examples.v`, `RefineEx.v` | examples with timings |

## What does not work yet

- `radcan_simplify` shows whatever normal form the normaliser chose: constant
  radicands stay split over the basis, rational constants are not put over a
  common denominator, numerals above 100000 show as `(Pos.to_nat p)%:R`; on
  Stdlib reals the result is in mathcomp notation (`rootR 2`, not `sqrt`).

- Rationalisation (Part 18) is all-or-nothing on a goal and adds the condition `E ≠ 0`,
  which can be a large polynomial.

- Refinement combines conditions only when they are linear in their monomials (`x*y`,
  `x^2` are independent unknowns).
- There is no factorisation into irreducibles: `x² − 1` is split into `(x−1)(x+1)` only if
  one of the factors appears in the goal.
- Absolute values only on real fields with roots (`rootR`, or a `realroot`): on a general
  `numFieldType`, `√((x−2)²) = x − 2` needs `2 <= x`.
- `√(1−x)·√(x−1) = 0` is not proved (it needs `x = 1`).
- Even roots of negatives (`√(−4)`) stay opaque on ℝ; on ℂ they use `ω_n`, without cyclotomic
  relations and without merging `ω_n` of different indices.
