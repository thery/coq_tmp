(* Differential corpus: the examples of the paper (Gonthier and Tassi, ITP
   2012), 1 to 10, with the paper's patterns and every pattern that
   select_all and point_to_pattern produce.  Run by run.sh. *)
From elpi Require Import elpi.
From coq_tmp.select.tests Require Import diff_support.
From Stdlib Require Import List.

Module Paper.
Section Ring.
Variables (R : Type) (zero two : R) (add mul : R -> R -> R) (opp : R -> R).
Variables (f : R -> R) (f2 : R -> R -> R).
Declare Scope ring_scope.
Delimit Scope ring_scope with ring.
Local Notation "0" := zero : ring_scope.
Local Notation "2" := two : ring_scope.
Local Notation "x + y" := (add x y) : ring_scope.
Local Notation "x * y" := (mul x y) : ring_scope.
Local Notation "- x" := (opp x) : ring_scope.
Local Notation "x - y" := (add x (opp y)) : ring_scope.
Local Open Scope ring_scope.

Goal forall a b c : R, a + (b * c - a) + a = b * c + a.
intros a b c.
elpi diff_cases "paper.ex1" "[_ - a]" "[b * c + _]" "[_ + _]".
elpi diff_gen "paper.ex1g".
Abort.

Goal forall a b c : R, a + (b * c + a) + a = b * c + a.
intros a b c.
elpi diff_cases "paper.ex2" "[_ - a]" "[b * c + _]".
elpi diff_gen "paper.ex2g".
Abort.

Goal forall a b c d : R, (a - b) + (b - c) = (a - b) + (d - b).
intros a b c d.
elpi diff_cases "paper.ex5" "[_ - b]" "{2}[_ - b]" "{1 2}[_ - b]" "{-1}[_ - b]" "{3}[_ - b]".
elpi diff_gen "paper.ex5g".
Abort.

Goal forall a b c : R, 0 = snd (0 * c, 0 * (a + b)).
intros a b c.
elpi diff_cases "paper.ex6" "[X in snd (_, X)]" "[0 * _]".
elpi diff_gen "paper.ex6g".
Abort.

Goal forall a b c : R, a + b = f (a * a + b) - c.
intros a b c.
elpi diff_cases "paper.ex7" "(_ + b in X in _ = X)" "(_ + b)" "(_ + b in RHS)".
elpi diff_gen "paper.ex7g".
Abort.

Goal forall a b c d : R, f2 (a + b) (2 * (a + c)) + (c + d) + f2 a (c + d) = 0.
intros a b c d.
elpi diff_cases "paper.ex8" "[_ + d as X in f2 _ X]" "[X in f2 _ X]" "[in f2 _ _]".
elpi diff_gen "paper.ex8g".
Abort.

Goal forall a b d : R, a + b + (a * ((a + b) * d)) = 0.
intros a b d.
elpi diff_cases "paper.ex9" "((_ + _) in X in (_ * X))" "(_ + _)".
elpi diff_gen "paper.ex9g".
Abort.
End Ring.
End Paper.

(* Ex. 3: graph is defined with map; the pattern [graph _ n] matches graph,
   [map _ _] does not (keyed matching: map is not the head) *)
Definition graph (f : nat -> nat) n := map f (seq 0 n).
Goal forall (f g : nat -> nat) n, graph (fun x => f (g x)) n = graph g n.
intros f g n.
elpi diff_cases "paper.ex3" "[graph _ n]" "[map _ _]" "[graph g _]".
elpi diff_gen "paper.ex3g".
Abort.

(* Ex. 10: the first phase has no reduction: _ + (_ + _) is m + (m + n),
   not n + 2 * m (which is n + (m + (m + 0)) by computation) *)
Goal forall n m : nat, n + 2 * m = m + (m + n).
intros n m.
elpi diff_cases "paper.ex10" "(_ + (_ + _))" "(n + _)" "(_ + (m + 0))".
elpi diff_gen "paper.ex10g".
Abort.

(* section 3.2: the occurrences of 1 + m are compared argument by argument:
   1 + (0 + m) is one, 0 + (1 + m) is not *)
Goal forall m : nat, (1 + m) + (1 + (0 + m)) + (0 + (1 + m)) = 0.
intros m.
elpi diff_cases "paper.s32" "(1 + _)" "(_ + m)".
elpi diff_gen "paper.s32g".
Abort.
