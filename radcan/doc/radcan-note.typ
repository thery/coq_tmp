#set page(paper: "a4", margin: 2.4cm, numbering: "1")
#set text(font: "New Computer Modern", size: 10.5pt)
#set par(justify: true, leading: 0.62em)
#set heading(numbering: "1.1", supplement: [section])
#set list(marker: [-])
#show heading: it => block(above: 1.2em, below: 0.7em)[#it]
#show raw: set text(font: "DejaVu Sans Mono", size: 9pt)
#show regex("\\b(Rocq|OCaml|Radcan)\\b"): smallcaps

// File names link to the sources on GitHub.
#let repo = "https://github.com/thery/coq_tmp/blob/main/radcan/"
#let src(f) = link(repo + f, raw(f))

#let tbl(headers, ..rows) = align(center)[
  #table(
    columns: headers.len(),
    stroke: none,
    inset: (x: 7pt, y: 3.5pt),
    align: (col, _) => if col == 0 { left } else { right },
    table.hline(),
    table.header(..headers.map(h => text(weight: "bold", h))),
    table.hline(stroke: 0.5pt),
    ..rows.pos().flatten(),
    table.hline(),
  )
]

#let ltbl(headers, ..rows) = align(center)[
  #table(
    columns: headers.len(),
    stroke: none,
    inset: (x: 7pt, y: 3.5pt),
    align: left,
    table.hline(),
    table.header(..headers.map(h => text(weight: "bold", h))),
    table.hline(stroke: 0.5pt),
    ..rows.pos().flatten(),
    table.hline(),
  )
]

#align(center)[
  #text(size: 17pt)[*Radcan in Rocq*]

  #v(0.9em)
  #text(size: 11pt)[Laurent Théry]

  #v(0.2em)
  #text(size: 9.5pt)[INRIA, Stamp Team \ #link("mailto:Laurent.Thery@inria.fr")[Laurent.Thery\@inria.fr]]
]

#v(1.4em)

#align(center)[#block(width: 88%, inset: (x: 0pt))[
  #set text(size: 9.8pt)
  #set par(justify: true)
  #set align(left)
  *Abstract.*
  In 1976, Caviness and Fateman described Radcan, the program of the Macsyma
  system that simplifies expressions with roots, such as
  $sqrt(12) - sqrt(3) = sqrt(3)$. This note presents a tactic for the Rocq
  prover that proves such equalities. The tactic works by _reflection_: the
  simplification is a program written in Rocq, run inside Rocq, and proved
  correct once. Many simplifications are only true under a condition, for
  example $sqrt(x^2) = x$ needs $0 <= x$. The tactic does not hide these
  conditions: it gives them back to the user. We follow the paper and try
  all its examples. On the way, the tactic found two misprints in it.

  #v(0.4em)
  *Keywords.* radicals, simplification, proof by reflection, Rocq,
  Mathematical Components.
]]

#v(0.6em)

= The problem

Here are some equalities between expressions with roots:

$ sqrt(2) dot sqrt(3) = sqrt(6) quad quad
  (1 + sqrt(2))^2 = 3 + 2 sqrt(2) quad quad
  1 / (1 + sqrt(2)) = sqrt(2) - 1 quad quad
  root(3, 2) dot sqrt(2) = root(6, 32). $

They are easy to check by hand, but tedious to prove in a proof assistant.
Each one needs a few rewriting steps, and each step has a small side
condition (a root is only well behaved on nonnegative numbers). We want one
tactic that proves them all.

The paper of Caviness and Fateman @caviness76 explains how the program
Radcan of the Macsyma system simplifies such expressions. The idea is to
put every expression in a _normal form_. Two expressions are equal when
their normal forms are equal. For example, both sides of
$sqrt(12) - sqrt(3) = sqrt(3)$ have the normal form $sqrt(3)$, because
$sqrt(12) = sqrt(4 dot 3) = 2 sqrt(3)$.

This note follows the paper and adapts it to Rocq. We do not repeat the
mathematics of the paper. We explain what changes when the result must be a
formal proof. All the examples below are checked by Rocq: they are taken
from the tutorial files of the development.

= Roots in Rocq

We use the Rocq prover @rocq and its Mathematical Components library
@mathcomp. The tactic must work for the real numbers and for the complex
numbers, and these two worlds do not have the same roots. So we start with
an interface. A _root structure_ on a field `F` is a function `proot` with
three properties (file #src("rocq/PosRoot.v")):

```coq
Record posroot (F : numFieldType) := PosRoot {
  proot : nat -> F -> F;
  proot_ge0 : forall n a, (0 < n)%N -> 0 <= a -> 0 <= proot n a;
  prootK : forall n a, (0 < n)%N -> 0 <= a -> proot n a ^+ n = a;
  prootM : forall n a b, (0 < n)%N -> 0 <= a -> 0 <= b ->
    proot n (a * b) = proot n a * proot n b
}.
```

`proot n a` is the $n$-th root of $a$. The first property says that the
root is nonnegative. The second says that its $n$-th power gives back $a$.
The third says that the root of a product is the product of the roots. All three only hold when $a >= 0$.
This restriction is important. Without it, we could prove

$ 1 = sqrt(1) = sqrt((-1) dot (-1)) = sqrt(-1) dot sqrt(-1) = -1. $

There are three instances of this interface:

- on the complex numbers, `n.-root`, the root of Mathematical Components;
- on any real closed field, `rootR`, a root that we define with the
  intermediate value theorem (#src("rocq/RootR.v"));
- on the real numbers of the Rocq standard library, `sqrt`. For this we
  borrow from MathComp-Analysis @analysis the file that makes them a real
  closed field (#src("rocq/Rstruct.v")).

In the examples, `r` is a fixed root structure and we use two local
notations: `\sqrt a` for `proot r 2 a` and `n.-proot a` for `proot r n a`.

```coq
Local Notation "n .-proot" := (proot r n) (at level 2, format "n .-proot").
Local Notation "\sqrt a" := (proot r 2 a) (at level 10).
```

With the interface alone, small facts already need some work. Here is
$sqrt(2) dot sqrt(3) = sqrt(6)$ proved by hand:

```coq
Lemma sqrt2_sqrt3 : \sqrt 2 * \sqrt 3 = \sqrt 6.
Proof. by rewrite -prootM // -natrM. Qed.
```

With the tactic, it is just `radcan`.

= Proof by reflection

Radcan is a program. We want to run it inside Rocq, so we write it in the
language of Rocq. To connect the program with the goal, we use the method
called _proof by reflection_. It has three parts.

*Syntax.* Expressions become data, a tree (#src("rocq/Syntax.v")):

```coq
Inductive rexpr : Type :=
  | RCst  : Z -> rexpr                     (* integer constant  *)
  | RVar  : nat -> rexpr                   (* a variable        *)
  | RRoot : positive -> positive -> rexpr  (* root of a number  *)
  | RRootE : positive -> rexpr -> rexpr    (* root of anything  *)
  | RAdd  : rexpr -> rexpr -> rexpr
  | ROpp  : rexpr -> rexpr
  | RSub  : rexpr -> rexpr -> rexpr
  | RMul  : rexpr -> rexpr -> rexpr
  | RPow  : rexpr -> nat -> rexpr
  | RInv  : rexpr -> rexpr.
```

A function `rinterp r env e` gives the value of the tree `e` in the field,
where `env` lists the values of the variables. For example the tree
`RMul (RRoot 2 2) (RRoot 2 3)` has the value `\sqrt 2 * \sqrt 3`.

*Computation.* A function `radcan_check e1 e2` computes the normal forms of
the two trees and compares them. It returns the list of conditions it used,
or nothing when the normal forms differ. It computes with integers and
rationals only, so the Rocq virtual machine runs it fast.

*Correctness.* One theorem, proved once and for all, connects the two:

```coq
Theorem radcan_eq_cond (F : numFieldType) (r : posroot F) env e1 e2 cs :
  radcan_check e1 e2 = Some cs -> all_conds r env cs ->
  rinterp r env e1 = rinterp r env e2.
```

The tactic `radcan` does the rest. It reads the goal and builds the two
trees. This step is written in the Ltac language. Then it runs
`radcan_check` and applies the theorem. The conditions `cs` are left as new
goals.

The program uses many algorithms: factoring integers and polynomials,
greatest common divisors, inverting a matrix. We never prove these
algorithms correct. Instead, each result is _checked_. For example, when the
program says that $12 = 2^2 dot 3$, it multiplies $2^2 dot 3$ and compares
with $12$. Only the check is part of the proof. This keeps the proofs small,
and lets us use fast algorithms that would be very hard to prove.

= Numbers under roots

The first version only knows roots of positive integers. Its normal form is
a sum of terms $c dot root(n_1, p_1)^(e_1) dots.c root(n_k, p_k)^(e_k)$ where
the $p_i$ are prime and the exponents are small (see the paper,
section 2). This already covers our first examples (#src("tutorial/Tut6_radcan.v")):

```coq
Lemma g1 : \sqrt 2 * \sqrt 3 = \sqrt 6. Proof. radcan. Qed.
Lemma g2 : (1 + \sqrt 2) ^+ 2 = 3 + 2 * \sqrt 2. Proof. radcan. Qed.
Lemma g3 : \sqrt 8 = 2 * \sqrt 2. Proof. radcan. Qed.
Lemma g4 : 3.-proot 2 * \sqrt 2 = 6.-proot 32. Proof. radcan. Qed.
Lemma g5 : \sqrt 12 - \sqrt 3 = \sqrt 3. Proof. radcan. Qed.
```

The same tactic works with the roots of the complex numbers and of the
standard library:

```coq
Lemma c1 (C : numClosedFieldType) : (3.-root 2) * (2.-root 2) = 6.-root 32 :> C.
Proof. radcan. Qed.

Lemma l3 : sqrt 12 - sqrt 3 = sqrt 3.
Proof. radcan_lra. Qed.
```

For a division, we make the denominator a plain number, as at school: $1 \/ (1 + sqrt(2)) = (sqrt(2) - 1) \/ ((sqrt(2)+1)(sqrt(2)-1)) = sqrt(2) - 1$.
The program finds the multiplier by linear algebra. The check is again a
multiplication (#src("tutorial/Tut8_div.v")):

```coq
Lemma d2 : 1 / (1 + \sqrt 2) = \sqrt 2 - 1. Proof. radcan. Qed.
Lemma d5 : 1 / (1 + \sqrt 2 + \sqrt 3) = (2 + \sqrt 2 - \sqrt 6) / 4.
Proof. radcan. Qed.
```

Large numbers are no problem: the numbers stay in binary, and the integers
are factored by small primes and greatest common divisors only.

```coq
Lemma b1 : sqrt (1000000007 ^ 2 * 3) = 1000000007 * sqrt 3.
Proof. radcan_Rstd. radcan. Qed.
```

= Variables and conditions

Now the variables. A variable outside a root behaves like in a polynomial:

```coq
Lemma v4 : (x - y * \sqrt 3) * (x + y * \sqrt 3) = x ^+ 2 - 3 * y ^+ 2.
Proof. radcan. Qed.
```

A variable under a root is a different story. The paper (section 3)
chooses fixed rules, and with these rules $sqrt(x^2) = x$. In the paper $x$
is a symbol, not a number. In Rocq, $x$ is a number, and $sqrt(x^2) = x$ is
false for $x = -1$. So, each time the program uses a rule that is only true
under a condition, it records the condition. The tactic gives the conditions
back to the user as new goals:

```coq
Lemma c1 : 0 <= x -> \sqrt (x ^+ 2) = x.
Proof. move=> x_ge0. radcan. exact: x_ge0. Qed.
```

Here is the example that started this work:
$sqrt(x^2 - 1) \/ sqrt(x - 1) = sqrt(x + 1)$. The program writes $x^2 - 1$
as $(x-1)(x+1)$, splits the root, and cancels. Splitting needs
$0 <= x - 1$ and $0 <= x + 1$, cancelling needs $x - 1 != 0$. Three
conditions in all. They are correct but not very readable, so a second
program _refines_ them. Here they become a single condition:

```coq
Lemma f1 : 1 < x ->
  \sqrt (x ^+ 2 - 1) / \sqrt (x - 1) = \sqrt (x + 1).
Proof. move=> h. radcan. exact: h. Qed.
```

The refinement only uses reasoning that is true in every field. So the same
tactic works on the complex numbers, where $0 <= x^2$ is false. Its result
is also checked. A proved function verifies that the new conditions imply
the old ones. The refinement knows intervals, combinations of bounds, and
the sign of constants with roots, for example $0 <= 3 - 2 sqrt(2)$.

On the standard reals, `radcan_lra` sends the conditions to the tactic
`lra`, so the example becomes one line:

```coq
Lemma l1 (x : R) : 1 < x -> sqrt (x ^ 2 - 1) / sqrt (x - 1) = sqrt (x + 1).
Proof. move=> h. radcan_lra. Qed.
```

On real fields, even roots of even powers give absolute values, with no
condition at all, and odd roots work for any sign:

```coq
Lemma a1 : rootR 2 ((x - 2) ^+ 2) = `|x - 2|.  Proof. by radcan. Qed.
Lemma o2 : rootR 3 (- 8 * x ^+ 3) = - 2 * x.   Proof. by radcan. Qed.
```

= What the program knows

We have added to the first version, step by step, what the paper describes.
Here is a summary with one example for each step.

#ltbl(([step], [example]),
  ([same base, different indices], [$sqrt(x) dot root(3, x) = root(6, x^5)$, if $0 <= x$]),
  ([factors of a radicand], [$sqrt(x^2 + 2x + 1) = x + 1$, if $-1 <= x$]),
  ([several variables], [$sqrt(x^2 - y^2) = sqrt(x - y) dot sqrt(x + y)$]),
  ([cancelling polynomials], [$(x^2 - 1) \/ (x - 1) = x + 1$, if $x != 1$]),
  ([roots in the denominator], [$(x - y) \/ (sqrt(x) + sqrt(y)) = sqrt(x) - sqrt(y)$]),
  ([roots of fractions], [$sqrt((x-1)\/(x+2)) = sqrt(x - 1) \/ sqrt(x + 2)$]),
  ([roots of roots], [$sqrt(x^2 + 3x + 3 + sqrt(x+1) sqrt(x+1)) = x + 2$]),
  ([negative numbers, reals], [$root(3, -8) = -2$]),
  ([negative numbers, complex], [$sqrt(-2) dot sqrt(-8) = -4$]),
)

The factors of polynomials are found by classic algorithms: square-free
decomposition @yun76, greatest common divisors @gcdheu, factoring in one and
in several variables @wang78. Denominators are cleared by a fraction-free
elimination @bareiss68. None of them is proved, all their results are
checked.

The complex numbers need care. Mathematical Components chooses one root
among the $n$ possible ones, the _principal_ root. With this choice the
root of a product is not always the product of the roots. So we write a
negative number as a positive one times a root of $-1$. For the small roots
of $-1$, we also prove their values:

$ root(3, -1) = (1 + sqrt(3) dot i) / 2 quad quad
  root(4, -1) = sqrt(2) / 2 (1 + i). $

Later we went further. We write $omega_n$ for $root(n, -1)$, the principal
root, that is $e^(i pi \/ n)$. The tactic now knows two general laws. The
first relates the roots of $-1$ of different orders: $omega_(n k)^k =
omega_n$. The second says that $omega_n$ is a root of a known polynomial,
the _cyclotomic_ polynomial. So it proves, for example,

```coq
Lemma u2 : 3.-root (-1 : C) ^+ 2 - 3.-root (-1) + 1 = 0.
Proof. by radcan. Qed.

Lemma u10 : 5.-root (-1 : C) ^+ 4 - 5.-root (-1) ^+ 3
          + 5.-root (-1) ^+ 2 - 5.-root (-1) + 1 = 0.
Proof. by radcan. Qed.
```

The cyclotomic polynomial is computed by the program and then checked, as
for factors. The two laws themselves are theorems, see
@sec-theorems.

Finally, we have also added some things that the paper does not do. The
tactic can _denest_ some roots of roots. It can _simplify_ a term instead of
proving an equality, like `ring_simplify`. It can also work with symbols
given by hypotheses (see the next section):

```coq
Lemma d1 : \sqrt (3 + 2 * \sqrt 2) = 1 + \sqrt 2.
Proof. radcan. Qed.

Lemma m1 : \sqrt (10 + 2 * \sqrt 6 + 2 * \sqrt 10 + 2 * \sqrt 15)
         = \sqrt 2 + \sqrt 3 + \sqrt 5.
Proof. radcan. Qed.
```

= The examples of the paper

We have run the tactic on all the examples of the paper. They are in
#src("paper/Paper.v").

#ltbl(([example], [result]),
  ([equation (1)], [proved, with $0 <= x$, $0 <= y$, $x != y$]),
  ([equation (8)], [proved]),
  ([section 2, the factors of radicands], [proved]),
  ([section 2, the root of roots], [proved, with $-1 <= x$]),
  ([equations (4) and (6)], [proved, with $-1 <= x^2$]),
  ([equation (3) as printed], [*refused*: it is false]),
  ([the polynomial $E$ as printed], [*refused*: $54 x$ should be $108 x$]),
  ([equation (3), in factored form], [proved, with $E != 0$]),
  ([equation (3) with $x^6$ for $x^5$], [proved, with $E != 0$]),
  ([equation (2)], [see below]),
)

So the tactic found two misprints in the paper. Equation (3) gives
$1 \/ (x + sqrt(2) + 3^(2\/3))$ as a fraction. A quick numerical test at
$x = 5\/2$ shows that the printed formula is wrong. Its numerator is right,
but its denominator starts with $x^5$ instead of $x^6$. The same happens for
the polynomial $E$ at the end of section 2: the coefficient of $x$ is $108$,
not $54$. Once corrected, both are proved.

Equation (2) is the most interesting one:

$ (x - 1)^(1\/4) / (1 - x)^(1\/4) - (x - 1)^(3\/4) / (1 - x)^(3\/4) - sqrt(2) = 0. $

With the principal roots of the complex numbers, it is false. When $x > 1$,
the left side is $-sqrt(2)$, and the tactic proves exactly that. The paper
reads it in another way. A root is a _symbol_ $u$ with an equation $u^4 = x - 1$,
and $(x-1)^(3\/4)$ means $u^3$. To prove equalities in this reading, the
tactic `radcan_sym` takes the symbols and their equations from the
hypotheses. It then proves equalities that hold for _every_ choice of the
roots:

```coq
Hypotheses (hu : u ^+ 4 = x - 1) (hw : w ^+ 4 = -1) (hz : z = w * u).

Lemma paper2 : x != 1 ->
  u / z - u ^+ 3 / z ^+ 3 - (w - w ^+ 3) = 0.
Proof. move=> h. radcan_sym. by rewrite subr_eq0. Qed.
```

Here $sqrt(2)$ is $w - w^3$, as in the paper. The condition $x != 1$ is
needed and the paper leaves it implicit: for $x = 1$, $u = 0$ and the
divisions make no sense.

= Some theorems proved on the way <sec-theorems>

To make the tactic work on the complex numbers, we had to prove some facts
that are interesting on their own. None of them uses trigonometry: there is
no $sin$ or $cos$ in Mathematical Components. They are about the principal
roots $root(n, x)$ of any algebraically closed field with an order, like
$CC$ (file #src("rocq/UnitArc.v")).

*Roots of $-1$.* The first two say how the roots $omega_n = root(n, -1)$
fit together:

```coq
Lemma rootC_N1_prim n : (0 < n)%N ->
  (2 * n).-primitive_root (n.-root (-1 : C)).
Lemma rootC_N1_index n k : (0 < n)%N -> (0 < k)%N ->
  (n * k).-root (-1 : C) ^+ k = n.-root (-1).
```

The first says that $omega_n$ has order exactly $2 n$. A comment in
Mathematical Components states it, but the proof was missing. Here is the idea
of the proof. Look at the $2 n$-th roots of 1 above the real axis, and take
the one with the largest real part. Multiplying by its conjugate moves any
other one closer to 1. Step by step, we reach 1, so all of them are its
powers.

*Roots of roots.* The second one generalises to every complex number,
with no condition at all (file #src("rocq/RootComp.v")):

```coq
Lemma rootC_mul n k (x : C) : (n * k).-root x = n.-root (k.-root x).
```

For real numbers this is easy. For complex numbers, the principal root
divides the angle of $x$. Dividing twice is the same as dividing once by
$n k$. The proof needs a small calculus of angles on the
circle, again without trigonometry.

*Gauss sums.* For an odd number $n$ and $zeta = e^(2 i pi \/ n)$, Gauss
proved in 1805 that

$ sum_(a = 0)^(n - 1) zeta^(a^2) = cases(sqrt(n) & "if" n = 1 med (mod 4),
  i sqrt(n) & "if" n = 3 med (mod 4)). $

That the square of the sum is $plus.minus n$ is easy algebra. The sign is
the hard part. Gauss wrote that it took him years. We follow his own
algebraic proof (file #src("rocq/GaussSum.v")). First, the sum is equal to a
product. Then the sign of each factor is given by the position of a root of
unity on the circle, which we already know.

```coq
Theorem gauss_sumC n : odd n -> gauss_sum n = 'i ^+ odd n./2 * sqrtC n%:R.
```

With this theorem, every square root of an integer can be written with
roots of unity, so the tactic can relate $sqrt(5)$ and $omega_5$.

*Cyclotomic polynomials.* The program computes the polynomial $Phi_m$
that is zero at a primitive root of unity of order $m$. We do not prove the
computation. Instead, a short lemma checks it with two multiplications
(file #src("rocq/Cyclo.v")):

```coq
Lemma prim_root_cert (R : idomainType) m (z : R) (p h g : {poly R}) D :
  m.-primitive_root z -> all (fun d => (0 < d < m)%N) D ->
  p * h = 'X^m - 1 -> h * g = \prod_(d <- D) ('X^d - 1) -> root p z.
```

*From angles to roots.* The real numbers of the Rocq standard library
have $cos$ and $sin$, but the complex roots of Mathematical Components know
nothing about angles. One lemma makes the link
(file #src("trig/TrigBridge.v")). With
$E(x) = cos x + i sin x$, for every $n > 0$:

$ cos(pi / n) + i sin(pi / n) = root(n, -1). $

```coq
Lemma E_root n : (0 < n)%N -> E (PI / INR n) = n.-root (-1 : R[i]).
```

The idea of the proof is simple. Since $E(pi \/ n)^n = E(pi) = -1$, it is
an $n$-th root of $-1$. Among all the $n$-th roots of $-1$, the principal
root is the one above the real axis with the largest real part. Here $sin$ gives the side of the axis, and $cos$
decreases on $[0, pi]$, so $E(pi \/ n)$ is that one.

*An olympiad problem.* Problem 5 of the 1963 International Mathematical
Olympiad asks to show

$ cos(pi / 7) - cos((2 pi) / 7) + cos((3 pi) / 7) = 1 / 2. $

We prove it on the real numbers of the Rocq standard library
(#src("tutorial/Tut35_imo1963.v")). The tactic knows nothing about $cos$,
so we go to the complex numbers. The number
$z = cos(pi \/ 7) + i sin(pi \/ 7)$ satisfies $z^7 = -1$. The cosines are
$(z^k + z^(-k)) \/ 2$, so the identity becomes algebra. By the lemma
above, $z$ is exactly $root(7, -1)$. Then the last step is just `radcan`:

```coq
Theorem imo1963 : cos (PI / 7) - cos (2 * PI / 7) + cos (3 * PI / 7) = 1 / 2.
```

= Trigonometric identities

Once the tactic knows the roots of unity, trigonometry is close. A second
tactic, `radcan_trig`, proves identities on the real numbers of the Rocq
standard library (file #src("trig/TrigTac.v")). It follows the route of the
olympiad problem. Each $cos x$ and $sin x$ is written with $E(x)$, angles
are turned into products and powers, and $E(pi \/ n)$ becomes $root(n, -1)$.
Then `radcan` does the algebra, and we come back to the real numbers.

```coq
Lemma cos3 x : cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x.
Proof. radcan_trig. Qed.

Lemma cos_PI5 : cos (PI / 5) = (1 + sqrt 5) / 4.
Proof. radcan_trig. Qed.
```

For $tan$ there are divisions, so there are conditions. The tactic gives
them back as real statements, or closes them with the hypotheses:

```coq
Lemma tanD x y : cos x <> 0 -> cos y <> 0 -> cos (x + y) <> 0 ->
  tan (x + y) = (tan x + tan y) / (1 - tan x * tan y).
Proof. move=> hx hy hxy. radcan_trig. Qed.
```

We have tried it on the usual list of identities. Here is a part of it;
each line takes one call, and less than a second unless said otherwise.

#ltbl(([identity], [remark]),
  ([$sin^2 x + cos^2 x = 1$], []),
  ([$cos(x + y)$, $sin(x + y)$, $tan(x + y)$], [conditions for $tan$]),
  ([$cos 3 x = 4 cos^3 x - 3 cos x$], []),
  ([$cos 10 x$ as a polynomial in $cos x$], [3.6 s]),
  ([$cos(x + y) cos(x - y) = cos^2 x - sin^2 y$], []),
  ([$cos(pi \/ 5) = (1 + sqrt(5)) \/ 4$], [uses a Gauss sum]),
  ([$tan(pi \/ 12) = 2 - sqrt(3)$], []),
  ([$cos(pi \/ 7) cos((2 pi) \/ 7) cos((3 pi) \/ 7) = 1 \/ 8$], []),
  ([$sin((2 pi) \/ 7) + sin((4 pi) \/ 7) - sin((6 pi) \/ 7) = sqrt(7) \/ 2$], [uses a Gauss sum]),
)

The full list is in the tutorial (Part 38). The tactic also has limits. It
only translates square roots of numbers. So
$cos(pi \/ 8) = sqrt(2 + sqrt(2)) \/ 2$ fails, but its square
$cos^2(pi \/ 8) = (2 + sqrt(2)) \/ 4$ is proved. It does not use
hypotheses that are equations, and it proves equalities only, not
inequalities.

= Conclusion

We hope we have shown that a classic algorithm of computer algebra fits well
in a proof assistant. The key points are reflection, which lets Rocq run
the program, and checking, which lets us use unproved algorithms without
risk. The new part is the treatment of the conditions. The paper fixes them
once and for all by rules. In Rocq they must be explicit, so the tactic
gives them back to the user, in a readable form.

The development is 62 Rocq files and 16 500 lines.

#tbl(([], [files], [lines]),
  ([roots: interface, instances, standard reals], [9], [1 300]),
  ([normal forms and the checker], [15], [5 100]),
  ([factoring polynomials], [4], [1 150]),
  ([refinement of conditions], [5], [1 650]),
  ([odd roots, roots of $-1$, real fields], [3], [150]),
  ([fractions, denesting, values of roots of $-1$], [4], [1 800]),
  ([roots of unity: index law, Gauss sums, cyclotomic reduction], [11], [2 700]),
  ([tactics, dispatch, simplification, symbols], [7], [1 800]),
  ([trigonometry (separate directory)], [4], [900]),
  ([*in all*], [*62*], [*16 500*]),
)

The tactics themselves are about 800 lines of Ltac. They only build the
trees, run the computation and apply the theorems. The theorems of the core
are proved without axioms. The standard reals, and their link with
Mathematical Components, bring their own axioms. On top of this come 37
tutorial files (3 200 lines), and the tests and the examples of the paper
(2 000 lines).

The tactic is not complete: when it fails, the equality may still be true.
This was not our goal, the paper treats this question in its section 4. We
have also left out the parts that the paper itself leaves out, such as the
general denesting of roots.

This development was written with the help of Claude, Anthropic's coding
assistant. The sources are at
#link("https://github.com/thery/coq_tmp/tree/main/radcan")[`github.com/thery/coq_tmp/radcan`],
with a long tutorial (`TUTORIAL.md`) and the paper transcribed beside them.

#bibliography("radcan-note.bib", title: [References], style: "springer-mathphys")
