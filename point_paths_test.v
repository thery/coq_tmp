(* Tests of point_run_path: selections given by the paths of the subterms
   (as Rocq's Set Printing Subterm Paths tags them in the goal display)
   instead of ranges of characters.  [elpi point_run_path_expect "Name"
   Line Sel ...] fails unless point_run_path gives the line Line; a
   selection is "P" (conclusion) or "H" "P" (hypothesis H).  Where the
   range method of point_run can be used, it is run on the same selection
   and gives the same line. *)

From Stdlib Require Import String.
From coq_tmp Require Import point_actions point_actions_more.

Definition double n := n + n.

(* the pbp example: 1 + 1 + a = double (1 + a); eq's arguments are at 1
   (its type, not printed), 2 and 3 *)
Goal forall a : nat, 1 + 1 + a = double (1 + a).
intros a.
elpi point_run_expect "Point" "pbp [X in X + _ = _]." "" 0 3.
elpi point_run_path_expect "Point" "pbp [X in X + _ = _]." "2.1".
elpi point_run_expect "Link" "pbp [X Y in X + _ = double Y]." "" 0 3 13 16.
elpi point_run_path_expect "Link" "pbp [X Y in X + _ = double Y]." "2.1" "3.1".
elpi point_run_path_expect "Simplify here" "rewrite [X in X + _ = _]/=." "2.1".
elpi point_run_path_expect "Unfold here" "rewrite [X in _ = X]/double." "3".
elpi point_run_path_expect "Name occurrence" "set x := {2}(a)." "3.1.2".
(* the whole conclusion *)
elpi point_run_path_expect "Point" "pbp [X in X]." "".
Abort.

(* a hypothesis *)
Goal forall a b : nat, a = b -> b = a.
intros a b ab.
elpi point_run_expect "Point" "move: ab; pbp [X in X = _ -> _]." "" ab 0 1.
elpi point_run_path_expect "Point" "move: ab; pbp [X in X = _ -> _]." "ab" "2".
elpi point_run_path_expect "Link" "move: ab; pbp [X Y in X = _ -> _ = Y]." "ab" "2" "3".
Abort.

(* the risky goals of point_print_test.v: a string with a non-breaking
   space, a product type in a hypothesis, a match whose branch binds
   variables, Printing All *)
Goal ("a b" = "a b")%string.
elpi point_run_path_expect "Point" "pbp [X in X = _]." "2".
Abort.

Goal forall (p : nat * nat), (let '(a, b) := p in a + b) = 0 -> True.
intros p H.
elpi point_run_path_expect "Point" "move: p; pbp [X in X * _ -> _]." "p" "1".
(* the scrutinee p: the range method widens it to the let, the path one
   selects it but its pattern does not elaborate (pbp_select, not the path) *)
elpi point_run_expect "Point" "move: H; pbp [X in X = _ -> _]." "let (a, b) := p in a + b" H 12 13.
Fail elpi point_run_path "Point" "H" "2.0".
Abort.

Goal forall (n : nat) (b : bool), match n with 0 => true | S k => Nat.eqb k n end = (if b then false else true).
intros n b.
elpi point_run_path_expect "Point" "pbp [X in match _ with | 0 => _ | S k => Nat.eqb _ X end = _]." "2.3.1.2".
elpi point_run_path_expect "Point" "pbp [X in match _ with | 0 => X | S k => _ end = _]." "2.2".
(* the binder of S k (the printer tags k with it) cannot be selected *)
Fail elpi point_run_path "Point" "2.3".
Abort.

Set Printing All.
Goal forall a b : nat, a + b = b + a /\ (a <= b \/ True).
intros a b.
elpi point_run_path_expect "Point" "pbp [X in X = _ /\ _]." "1.2".
Abort.
Unset Printing All.

(* errors *)
Goal forall n : nat, n = n.
intros n.
Fail elpi point_run_path "Point" "5".
Fail elpi point_run_path "Point" "x" "2".
Fail elpi point_run_path "Point" "2.x".
Fail elpi point_run_path "Link" "2".
Abort.
