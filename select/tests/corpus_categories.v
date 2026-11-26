(* Differential corpus by category: each Id is <category>.<n>; run.sh
   counts the cases per category.  Each goal also gets the patterns of
   select_all and point_to_pattern (diff_gen). *)
From Stdlib Require Import List.
From elpi Require Import elpi.
From coq_tmp.select.tests Require Import diff_support.
Import ListNotations.

(* forms: t, X in C, t in X in C, t as X in C, {k}, {k1 k2}, {-k} *)
Goal forall (f : nat -> nat -> nat) a b c, f (a + b) (b + c) = f (a + b) (c + b) + (a + b).
intros f a b c.
elpi diff_cases "forms.1" "(_ + b)" "(X in f X _)" "(X in f _ X)" "(_ + _ in X in f _ X)" "(_ + b as X in f _ X)" "{1}(_ + b)" "{2}(_ + b)" "{1 3}(_ + b)" "{-1}(_ + b)" "{-2 3}(_ + b)" "{4}(_ + b)" "{2}(X in f X _)" "{1}(_ + _ in X in f _ X)" "(a + b)" "{3}(a + b)" "(X in _ = _ + X)" "(b + _ in X in _ = X)" "(X in f _ X + _)".
elpi diff_gen "forms.1g".
Abort.

(* pre-order: an ancestor before its descendants, left before right,
   nested applications of the same key *)
Goal forall a b c : nat, (a + b) + c = a + (b + c) /\ (a * b) * (a * b) = 0.
intros a b c.
elpi diff_cases "order.1" "(_ + _)" "(_ + c)" "(a + _)" "(_ + (_ + _))" "((_ + _) + _)" "(_ * _)" "(a * _)" "(X in X * _)" "(X in _ * X)" "{2}(_ * _)" "(_ = _)" "{2}(_ = _)" "(X in _ = X /\ _)" "(X in _ /\ X)" "(_ /\ _)".
elpi diff_gen "order.1g".
Abort.

Goal forall f : nat -> nat, f (f (f 0)) = f (f 1).
intros f.
elpi diff_cases "order.2" "(f _)" "(f (f _))" "(f 1)" "(X in f (f X))" "{2}(f _)" "(f _ in X in _ = X)" "(f 0 as X in f (f X))".
elpi diff_gen "order.2g".
Abort.

(* occurrences: equal copies, copies equal up to conversion (compared
   argument by argument), numerals *)
Goal forall m : nat, 2 + m = (1 + 1) + m /\ S (S m) = 2 + m /\ 2 = 1 + 1.
intros m.
elpi diff_cases "occ.1" "(2 + m)" "(_ + m)" "(1 + 1)" "2" "(S _)" "(2 + _)" "{2}(2 + m)" "(X in X + m)" "(_ + _ in X in _ /\ X)".
elpi diff_gen "occ.1g".
Abort.

Definition twice (n : nat) := n + n.
Goal forall n : nat, twice n = n + n /\ twice (n + n) = twice n + twice n.
intros n.
elpi diff_cases "occ.2" "(twice _)" "(_ + _)" "(n + n)" "(twice n)" "{2}(twice _)" "(twice (_ + _))" "(_ + n)".
elpi diff_gen "occ.2g".
Abort.

(* keyed matching and conversion: phase 1 without reduction, phase 2 with
   it (paper, Ex. 10) *)
Goal forall n m : nat, n + 2 * m = m + (m + n) /\ 0 + n = n.
intros n m.
elpi diff_cases "conv.1" "(_ + (_ + _))" "(_ + (m + 0))" "(n + _)" "(_ * m)" "(2 * _)" "(0 + _)" "(_ + n)" "(n + (m + _))" "(X in n + X)".
elpi diff_gen "conv.1g".
Abort.

(* implicit and hidden arguments, casts *)
Goal forall (a : nat) (l : list nat), length (a :: l) = S (length l) /\ (a : nat) = a.
intros a l.
change (length (a :: l) = S (length l) /\ (a : nat) = a).
elpi diff_cases "hidden.1" "(length _)" "(_ :: _)" "(length l)" "nat" "(list nat)" "(@length nat _)" "(X in length X)" "a" "(X in X = _)" "(X in _ /\ X = _)" "{2}a" "(S _)".
elpi diff_gen "hidden.1g".
Abort.

(* binders: patterns under forall and fun, bound variables in the redex *)
Goal forall a : nat, (forall n : nat, n + a = a + n) /\ (fun k : nat => k + 0) a = a.
intros a.
elpi diff_cases "binders.1" "(_ + a)" "(a + _)" "(_ + 0)" "(X in _ + X)" "(forall n, _)" "(fun k : nat => _)" "(X in (fun k : nat => _) X = _)" "(_ = _)" "{3}(_ = _)" "(_ + _)".
elpi diff_gen "binders.1g".
Abort.

Goal forall a : nat, (forall n : nat, n + 0 = n) -> a + 0 = a.
intros a H.
elpi diff_cases "binders.2" "(_ + 0)" "(a + _)" "(X in X = _)".
elpi diff_cases "hyp.1" "in" "H" "(_ + 0)" "(_ = _)" "(X in _ = X)" "nat" "(forall n, _)".
elpi diff_gen "binders.2g".
Abort.

(* hypotheses *)
Goal forall (f : nat -> nat) a b, f a + f b = f (a + b) -> f (a + b) = f a + f b -> True.
intros f a b H1 H2.
elpi diff_cases "hyp.2" "in" "H1" "(f _)" "(X in _ = f X)" "(f _ in X in _ = X)" "{2}(f _)" "(f a + _)" "(_ + _ as X in f X)" "(a + _)".
elpi diff_cases "hyp.3" "in" "H2" "(f _)" "(X in X = _)" "(_ + _)" "{3}(f _)".
elpi diff_gen "hyp.2g".
Abort.

(* projections, canonical structures (paper, section 3.1): outside the
   fragment for the projection; a concrete operation is a constant *)
Structure monoid := Monoid { mT : Type; mop : mT -> mT -> mT }.
Canonical nat_monoid := Monoid nat plus.
Goal forall a b : nat, mop nat_monoid a b = a + b.
intros a b.
elpi diff_cases "proj.1" "(mop _ _ _)" "(mop _ a _)" "(_ + _)" "(plus _ _)" "(X in mop _ X _)".
elpi diff_gen "proj.1g".
Abort.

(* flexible head and other forms outside the fragment *)
Goal forall (f g : nat -> nat) a, f a = g a.
intros f g a.
elpi diff_cases "outside.1" "(_ a)" "(X in X a = _)" "(X in X)" "(let x := a in x)".
Abort.

(* failures: no instance, a closed term that does not occur, X absent *)
Goal forall a b : nat, a + b = b + a.
intros a b.
elpi diff_cases "fail.1" "(_ * _)" "(a * b)" "(X in _ * X)" "(_ * _ in X in _ = X)" "(a + a)" "{2}(a + a)" "(X in a + _)" "(_ + a in X in X = _)" "{3}(_ + _)".
Abort.

(* a match, a let, an if *)
Goal forall (n : nat) (b : bool), (if b then n else 0) = match n with 0 => 1 | S k => k end /\ (let x := n in x + x) = n.
intros n b.
elpi diff_cases "match.1" "(if _ then _ else _)" "n" "(_ + _)" "(X in (if _ then X else _) = _)" "(S _)" "0" "nat" "{2}n" "(X in (let x := X in _) = _)".
elpi diff_gen "match.1g".
Abort.

(* a hypothesis: set in H generalizes H over the conclusion *)
Goal forall a : nat, a + 0 = 0 -> (forall n : nat, n = n) -> a + 0 = a.
intros a H H'.
elpi diff_cases "hyp.4" "in" "H" "(a + 0)" "{1}(a + 0)" "{2}(a + 0)" "(_ = _)" "{2}(_ = _)" "(X in X = _)".
elpi diff_cases "hyp.5" "in" "H'" "(forall n, _)" "(_ = _)" "nat" "{2}(_ = _)".
Abort.
