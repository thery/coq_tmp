(* The cases of the subterm paths with mathcomp's notations (as
   point_paths_cases.v; checked by point_paths_roundtrip.sh when mathcomp
   is installed; not in _CoqProject).  mathcomp's binder notations
   (\sum_(i < n) F, [exists x, P], [seq E | x <- s], [forall x, P],
   \big[op/idx]_(i <- s) F, [set x | P]) print the names of a fun that
   is an argument: the printer does not tag those names (RT-UNTAGGED). *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop finset.
From coq_tmp Require Import point_actions.

(* \sum, \prod, \big with a bound, a range and a sequence *)
Goal forall (n : nat) (s : seq nat),
  \sum_(i < n) i = \sum_(0 <= j < n) j + \prod_(x <- s) x /\
  \big[addn/0]_(k <- s | odd k) k.*2 = 0.
move=> n s.
elpi point_paths_check.
Abort.

(* [exists x, P x], [forall x, P x] on a finite type, [seq ...], [set ...] *)
Goal forall (n : nat) (P : 'I_n -> bool) (s : seq nat),
  [exists x, P x] = [forall x, ~~ P x] /\
  [seq x + 1 | x <- s] = [seq x <- s | odd x] /\
  #|[set x | P x]| = 0.
move=> n P s.
elpi point_paths_check.
Abort.

(* in hypotheses *)
Goal forall (n : nat) (s : seq nat),
  \sum_(i < n) i = 0 -> [seq x * 2 | x <- s] = s -> True.
move=> n s H1 H2.
elpi point_paths_check.
Abort.
