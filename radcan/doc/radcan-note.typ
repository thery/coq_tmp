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

`proot n a` is the $n$-th root of $a$. The three properties say that the root
is nonnegative, that its $n$-th power gives back $a$, and that the root of a
product is the product of the roots. All three only hold when $a >= 0$.
This restriction is important. Without it, we could prove

$ 1 = sqrt(1) = sqrt((-1) dot (-1)) = sqrt(-1) dot sqrt(-1) = -1. $

There are three instances of this interface:

- on the complex numbers, `n.-root`, the root of Mathematical Components;
- on any real closed field, `rootR`, a root that we define with the
  intermediate value theorem (#src("rocq/RootR.v"));
- on the real numbers of the Rocq standard library, `sqrt`. For this we
  borrow from MathComp-Analysis @analysis the file that makes them a real
  closed field (#src("rocq/Rstruct.v")).

With the interface alone, small facts already need some work. Here is
$sqrt(2) dot sqrt(3) = sqrt(6)$ proved by hand:

```coq
Lemma sqrt2_sqrt3 : proot r 2 2 * proot r 2 3 = proot r 2 6.
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
`RMul (RRoot 2 2) (RRoot 2 3)` has the value `proot r 2 2 * proot r 2 3`.

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
trees (this step is written in the Ltac language), runs `radcan_check`,
applies the theorem, and leaves the conditions `cs` as new goals.

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
Lemma g1 : proot r 2 2 * proot r 2 3 = proot r 2 6. Proof. radcan. Qed.
Lemma g2 : (1 + proot r 2 2) ^+ 2 = 3 + 2 * proot r 2 2. Proof. radcan. Qed.
Lemma g3 : proot r 2 8 = 2 * proot r 2 2. Proof. radcan. Qed.
Lemma g4 : proot r 3 2 * proot r 2 2 = proot r 6 32. Proof. radcan. Qed.
Lemma g5 : proot r 2 12 - proot r 2 3 = proot r 2 3. Proof. radcan. Qed.
```

The same tactic works with the roots of the complex numbers and of the
standard library:

```coq
Lemma c1 (C : numClosedFieldType) : (3.-root 2) * (2.-root 2) = 6.-root 32 :> C.
Proof. radcan. Qed.

Lemma l3 : sqrt 12 - sqrt 3 = sqrt 3.
Proof. radcan_lra. Qed.
```

Divisions are handled by making the denominator a plain number, as at
school: $1 \/ (1 + sqrt(2)) = (sqrt(2) - 1) \/ ((sqrt(2)+1)(sqrt(2)-1)) = sqrt(2) - 1$.
The program finds the multiplier by linear algebra, and the check is
again a multiplication (#src("tutorial/Tut8_div.v")):

```coq
Lemma d2 : 1 / (1 + proot r 2 2) = proot r 2 2 - 1. Proof. radcan. Qed.
Lemma d5 : 1 / (1 + proot r 2 2 + proot r 2 3) =
           (2 + proot r 2 2 - proot r 2 6) / 4.
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
Lemma v4 : (x - y * proot r 2 3) * (x + y * proot r 2 3) = x ^+ 2 - 3 * y ^+ 2.
Proof. radcan. Qed.
```

A variable under a root is a different story. The paper (section 3)
chooses fixed rules, and with these rules $sqrt(x^2) = x$. In the paper $x$
is a symbol, not a number. In Rocq, $x$ is a number, and $sqrt(x^2) = x$ is
false for $x = -1$. So, each time the program uses a rule that is only true
under a condition, it records the condition. The tactic gives the conditions
back to the user as new goals:

```coq
Lemma c1 : 0 <= x -> proot r 2 (x ^+ 2) = x.
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
  proot r 2 (x ^+ 2 - 1) / proot r 2 (x - 1) = proot r 2 (x + 1).
Proof. move=> h. radcan. exact: h. Qed.
```

The refinement uses only reasoning that is true in every field: the same
tactic works on the complex numbers, where $0 <= x^2$ is false. Its result
is also checked: a proved function verifies that the new conditions imply
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
negative number as a positive one times a root of $-1$, and we use the
values of the small roots of $-1$, which we prove:

$ root(3, -1) = (1 + sqrt(3) dot i) / 2 quad quad
  root(4, -1) = sqrt(2) / 2 (1 + i). $

This is enough to prove, for example, $omega^2 - omega + 1 = 0$ for
$omega = root(3, -1)$:

```coq
Lemma u2 : 3.-root (-1 : C) ^+ 2 - 3.-root (-1) + 1 = 0.
Proof. by radcan. Qed.
```

Finally, we have also added some things that the paper does not do. The
tactic can _denest_ some roots of roots, it can _simplify_ a term instead of
proving an equality (like `ring_simplify`), and it can work with symbols
given by hypotheses (see the next section):

```coq
Lemma d1 : proot r 2 (3 + 2 * proot r 2 2) = 1 + proot r 2 2.
Proof. radcan. Qed.

Lemma m1 : proot r 2 (10 + 2 * proot r 2 6 + 2 * proot r 2 10
                         + 2 * proot r 2 15)
         = proot r 2 2 + proot r 2 3 + proot r 2 5.
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
  ([equation (3), corrected], [proved, with $E != 0$]),
  ([equation (2)], [see below]),
)

So the tactic found two misprints in the paper. Equation (3) gives
$1 \/ (x + sqrt(2) + 3^(2\/3))$ as a fraction. A quick numerical test at
$x = 5\/2$ shows that the printed formula is wrong. The same happens for
the polynomial $E$ at the end of section 2: the coefficient of $x$ is $108$,
not $54$. Once corrected, both are proved.

Equation (2) is the most interesting one:

$ (x - 1)^(1\/4) / (1 - x)^(1\/4) - (x - 1)^(3\/4) / (1 - x)^(3\/4) - sqrt(2) = 0. $

With the principal roots of the complex numbers, it is false: when $x > 1$
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

= Conclusion

We hope we have shown that a classic algorithm of computer algebra fits well
in a proof assistant. The key points are reflection, which lets Rocq run
the program, and checking, which lets us use unproved algorithms without
risk. The new part is the treatment of the conditions. The paper fixes them
once and for all by rules. In Rocq they must be explicit, so the tactic
gives them back to the user, in a readable form.

The development is 45 Rocq files and 12 600 lines.

#tbl(([], [files], [lines]),
  ([roots: interface, instances, standard reals], [9], [1 300]),
  ([normal forms and the checker], [16], [5 200]),
  ([factoring polynomials], [3], [1 000]),
  ([refinement of conditions], [5], [1 600]),
  ([odd roots, roots of $-1$, real fields], [3], [100]),
  ([fractions, denesting, roots of $-1$], [4], [1 800]),
  ([tactics, simplification, symbols], [5], [1 600]),
  ([*in all*], [*45*], [*12 600*]),
)

The tactics themselves are about 700 lines of Ltac. They only build the
trees, run the computation and apply the theorems. All the theorems are
proved without axioms (the standard reals bring their own axioms). On top of
this come 31 tutorial files (2 400 lines), and the tests and the examples of
the paper (1 900 lines).

The tactic is not complete: when it fails, the equality may still be true.
This was not our goal, the paper treats this question in its section 4. We
have also left out the parts that the paper itself leaves out, such as the
general denesting of roots.

This development was written with the help of Claude, Anthropic's coding
assistant. The sources are at
#link("https://github.com/thery/coq_tmp/tree/main/radcan")[`github.com/thery/coq_tmp/radcan`],
with a long tutorial (`TUTORIAL.md`) and the paper transcribed beside them.

#bibliography("radcan-note.bib", title: [References], style: "springer-mathphys")
