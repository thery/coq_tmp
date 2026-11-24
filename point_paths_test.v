(* Tests of point_run_path: selections given by the paths of the subterms
   (as Rocq's Set Printing Subterm Paths tags them in the goal display)
   instead of ranges of characters.  [elpi point_run_path_expect "Name"
   Line Ws Sel ...] fails unless point_run_path gives the line Line, with
   the warnings that the selection is widened to Ws (separated by " / ",
   "" for none); a selection is "P" (conclusion) or "H" "P" (hypothesis
   H).  Where the range method of point_run can be used, it is run on the
   same selection and gives the same line. *)

From Stdlib Require Import String.
From coq_tmp Require Import point_actions point_actions_more.

Definition double n := n + n.

(* the pbp example: 1 + 1 + a = double (1 + a); eq's arguments are at 1
   (its type, not printed), 2 and 3 *)
Goal forall a : nat, 1 + 1 + a = double (1 + a).
intros a.
elpi point_run_expect "Point" "pbp [X in X + _ = _]." "" 0 3.
elpi point_run_path_expect "Point" "pbp [X in X + _ = _]." "" "2.1".
elpi point_run_expect "Link" "pbp [X Y in X + _ = double Y]." "" 0 3 13 16.
elpi point_run_path_expect "Link" "pbp [X Y in X + _ = double Y]." "" "2.1" "3.1".
elpi point_run_path_expect "Simplify here" "rewrite [X in X + _ = _]/=." "" "2.1".
elpi point_run_path_expect "Unfold here" "rewrite [X in _ = X]/double." "" "3".
elpi point_run_path_expect "Name occurrence" "set x := {2}(a)." "" "3.1.2".
(* the whole conclusion *)
elpi point_run_path_expect "Point" "pbp [X in X]." "" "".
Abort.

(* a hypothesis *)
Goal forall a b : nat, a = b -> b = a.
intros a b ab.
elpi point_run_expect "Point" "move: ab; pbp [X in X = _ -> _]." "" ab 0 1.
elpi point_run_path_expect "Point" "move: ab; pbp [X in X = _ -> _]." "" "ab" "2".
elpi point_run_path_expect "Link" "move: ab; pbp [X Y in X = _ -> _ = Y]." "" "ab" "2" "3".
Abort.

(* the risky goals of point_print_test.v: a string with a non-breaking
   space, a product type in a hypothesis, a match whose branch binds
   variables, Printing All *)
Goal ("a b" = "a b")%string.
elpi point_run_path_expect "Point" "pbp [X in X = _]." "" "2".
Abort.

Goal forall (p : nat * nat), (let '(a, b) := p in a + b) = 0 -> True.
intros p H.
elpi point_run_path_expect "Point" "move: p; pbp [X in X * _ -> _]." "" "p" "1".
(* the scrutinee p: its pattern does not elaborate, so both methods widen
   it to the let *)
elpi point_run_expect "Point" "move: H; pbp [X in X = _ -> _]." "let (a, b) := p in a + b" H 12 13.
elpi point_run_path_expect "Point" "move: H; pbp [X in X = _ -> _]." "let (a, b) := p in a + b" "H" "2.0".
(* the binders a and b of the let (its branch), as the range method *)
elpi point_run_path_expect "Point" "move: H; pbp [X in X = _ -> _]." "let (a, b) := p in a + b" "H" "2.2".
elpi point_run_path_expect "Point" "move: H; pbp [X in X = _ -> _]." "let (a, b) := p in a + b" "H" "2.2.2".
Abort.

Goal forall (n : nat) (b : bool), match n with 0 => true | S k => Nat.eqb k n end = (if b then false else true).
intros n b.
elpi point_run_path_expect "Point" "pbp [X in match _ with | 0 => _ | S k => Nat.eqb _ X end = _]." "" "2.3.2.2".
elpi point_run_path_expect "Point" "pbp [X in match _ with | 0 => X | S k => _ end = _]." "" "2.2".
(* the binder of S k (the printer tags k with it): widened to the match *)
elpi point_run_path_expect "Point" "pbp [X in X = _]." "match n with | 0 => true | S k => Nat.eqb k n end" "2.3".
Abort.

(* the return type of a match: widened to the match *)
Goal forall (b : bool), match b as x return (if x then nat else bool) with true => 0 | false => true end = match b as x return (if x then nat else bool) with true => 0 | false => true end.
intros b.
elpi point_run_path_expect "Point" "pbp [X in X = _]." "if b as x return (if x then nat else bool) then 0 else true" "2.1.2".
elpi point_run_path_expect "Point" "pbp [X in _ = X]." "if b as x return (if x then nat else bool) then 0 else true" "3.1.2.0".
Abort.

(* a binder named as a hypothesis: the pattern names it as the goal
   display does (in a hypothesis: x, unchanged; in the conclusion: x0, the
   name Rocq gives it), not as Rocq-Elpi prints it (elpi_ctx_entry_3_) *)
Goal forall x : nat, (forall x : nat, x = x) -> forall y, (fun x => x + y) x = x.
intros x H.
elpi point_run_path_expect "Point" "move: H; pbp [X in (forall x : nat, X x) -> _]." "" "H" "2".
elpi point_run_path_expect "Point" "move: H; pbp [X in (forall x : nat, X x = _) -> _]." "" "H" "2.2".
elpi point_run_path_expect "Point" "pbp [X in forall y : nat, [x0 : nat in X x0 + _] _ = _]." "" "2.2.0.2.1".
(* the type of the fun: the pattern keeps the application (no beta
   reduction), the type is X *)
elpi point_run_path_expect "Point" "pbp [X in forall y : nat, [x0 : X in _] _ = _]." "" "2.2.0.1".
(* the type of a binder that the rest depends on: widened to the binder *)
elpi point_run_path_expect "Point" "move: H; pbp [X in X -> _]." "forall x : nat, x = x" "H" "1".
elpi point_run_path_expect "Point" "pbp [X in X]." "forall y : nat, [x0 : nat in x0 + y] x = x" "1".
Abort.

Goal forall (a b : nat) (c d : bool), (fun x y : nat => x + y) a b = a + b /\ exists (u v : nat) (w : bool), u = v /\ w = c.
(* the type of u in exists (u v : nat): widened to the exists, as the
   range method *)
elpi point_run_path_expect "Point" "pbp [X in forall (a b : nat) (c : bool), _ -> _ /\ X c]." "exists (u v : nat) (w : bool), u = v /\ w = c" "2.2.2.2.2.2.2.2.1".
Abort.

(* a cast (Rocq-Elpi sees it as a let): the pattern is a cast *)
Goal forall n : nat, (n : nat) = n.
intros n.
change ((n : nat) = n).
elpi point_run_expect "Point" "pbp [X in (X : nat) = _]." "" 1 2.
elpi point_run_path_expect "Point" "pbp [X in (X : nat) = _]." "" "2.1".
Abort.

(* a term under a coercion that is not printed: n in (n + 1)%Z is
   Z.of_nat n; the selection is the coercion, which prints as n (no
   warning), as the range method *)
Module C.
From Stdlib Require Import ZArith.
Coercion Z.of_nat : nat >-> Z.
Record box := Box { unbox :> nat }.
Goal forall (n : nat) (b : box), (n + 1 = b)%Z /\ b + 0 = n.
intros n b.
elpi point_run_expect "Point" "pbp [X in (X + _)%Z = _ /\ _]." "" 1 2.
elpi point_run_path_expect "Point" "pbp [X in (X + _)%Z = _ /\ _]." "" "1.2.1.1".
elpi point_run_path_expect "Point" "pbp [X in _ = X /\ _]." "" "1.3.1.1".
elpi point_run_path_expect "Point" "pbp [X in _ /\ X + _ = _]." "" "2.2.1.1".
Abort.
End C.

Set Printing All.
Goal forall a b : nat, a + b = b + a /\ (a <= b \/ True).
intros a b.
elpi point_run_path_expect "Point" "pbp [X in X = _ /\ _]." "" "1.2".
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

(* the scrutinee of an if: the text (IF X THEN _ ELSE _) does not
   elaborate (X has no type: if X then .. is a match on X), so X is written
   with its type, as the range method does; rewrite accepts it (Simplify
   here) *)
Module IfMatch.
Notation "'IF' c 'THEN' a 'ELSE' b" := (if c then a else b) (at level 200).
Goal forall (b : bool) (n : nat), (IF b THEN n ELSE 0) = n.
intros b n.
elpi point_run_expect "Point" "pbp [X in (IF X : bool THEN _ ELSE _) = _]." "" 3 4.
elpi point_run_path_expect "Point" "pbp [X in (IF X : bool THEN _ ELSE _) = _]." "" "2.0".
elpi point_run_path_expect "Simplify here" "rewrite [X in (IF X : bool THEN _ ELSE _) = _]/=." "" "2.0".
Abort.
End IfMatch.

(* the same without the notation: if b then n else 0 *)
Goal forall (b : bool) (n : nat), (if b then n else 0) = n.
intros b n.
elpi point_run_expect "Point" "pbp [X in (if X : bool then _ else _) = _]." "" 3 4.
elpi point_run_path_expect "Point" "pbp [X in (if X : bool then _ else _) = _]." "" "2.0".
Abort.

(* the scrutinee of a match whose patterns give its type: no type added *)
Goal forall n : nat, match n with 0 => true | S _ => false end = true.
intros n.
elpi point_run_expect "Point" "pbp [X in match X with | 0 => _ | S _ => _ end = _]." "" 5 6.
elpi point_run_path_expect "Point" "pbp [X in match X with | 0 => _ | S _ => _ end = _]." "" "2.0".
Abort.

(* binder names: the path of a name is the index 0 of its binder (forall,
   fun, let; the branches of a match are funs); a name is not a subterm:
   the binder is selected, with a warning, and a path through a name is an
   error *)
Goal forall n : nat, n + 0 = n.
elpi point_run_path_expect "Point" "pbp [X in X]." "forall n : nat, n + 0 = n (a binder name: the whole forall is selected)" "0".
elpi point_run_path_expect "Point" "pbp [X in forall n : nat, X n + _ = _]." "" "2.2.1".
Fail elpi point_run_path "Point" "0.1".
Abort.

Goal forall n : nat, (let m := n + 1 in m * m) = n /\ (fun k : nat => k) n = n.
intros n.
elpi point_run_path_expect "Point" "pbp [X in X = _ /\ _]." "let m := n + 1 in m * m (a binder name: the whole let is selected)" "1.2.0".
elpi point_run_path_expect "Point" "pbp [X in (let m := X in _) = _ /\ _]." "" "1.2.2".
elpi point_run_path_expect "Point" "pbp [X in (let m := _ in X m) = _ /\ _]." "" "1.2.3".
elpi point_run_path_expect "Point" "pbp [X in _ /\ X _ = _]." "[k : nat in k] (a binder name: the whole fun is selected)" "2.2.0.0".
Abort.

Goal forall (n : nat), match n with 0 => true | S k => Nat.eqb k n end = true -> (forall z : nat, z = z) -> True.
intros n H H'.
(* the name k of the branch S k: its fun cannot be selected, the match is *)
elpi point_run_path_expect "Point" "move: H; pbp [X in X = _ -> _]." "match n with | 0 => true | S k => Nat.eqb k n end (a binder name)" "H" "2.3.0".
elpi point_run_path_expect "Point" "move: H'; pbp [X in X -> _]." "forall z : nat, z = z (a binder name: the whole forall is selected)" "H'" "0".
Abort.

(* the show actions (point_actions_show.v): their message is printed as a
   line is; on a subterm of the conclusion, of a hypothesis, under a
   binder, on a binder name; the errors *)
From coq_tmp Require Import point_actions_show.
Lemma two_is : 2 = 1 + 1. Proof. reflexivity. Qed.
Goal forall a : nat, double (1 + a) = 2 + a + a -> forall n : nat, n + double a = a.
intros a H.
elpi point_run_path_expect "Type of" "nat : Set" "" "1".
elpi point_run_path_expect "Check this" "nat
     : Set" "" "1".
elpi point_run_path_expect "Type of" "n : nat" "" "0".
elpi point_run_path_expect "Where defined" "n: a variable bound by a forall of the goal" "" "0".
elpi point_run_path_expect "Where defined" "n: a variable bound by a forall of the goal" "" "2.2.1".
elpi point_run_path_expect "Type of" "double : nat -> nat" "" "2.2.2.0".
elpi point_run_path_expect "Unfolds to" "double a ⇒ a + a  (coq_tmp.point_paths_test.double unfolded)" "" "2.2.2".
elpi point_run_path_expect "Where defined" "coq_tmp.point_paths_test.double: a definition, in the library coq_tmp.point_paths_test" "" "H" "2".
elpi point_run_path_expect "Where defined" "a: a hypothesis of the goal (a local variable)" "" "H" "2.1.2".
elpi point_run_path_expect "Unfolds to" "double (1 + a) ⇒ 1 + a + (1 + a)  (coq_tmp.point_paths_test.double unfolded)" "" "H" "2".
Abort.
Goal forall a : nat, (if true then a else 0) = double 2.
intros a.
elpi point_run_path_expect "Head normal form" "if true then a else 0 ⇒ a" "" "2".
elpi point_run_path_expect "Normal form" "double 2 ⇒ 4" "" "3".
Fail elpi point_run_path "Where defined" "2".
Fail elpi point_run_path "Type of" "2.2" "2.3".
Abort.
Goal two_is = two_is.
elpi point_run_path_expect "Where defined" "coq_tmp.point_paths_test.two_is: a lemma or an opaque definition (Qed), in the library coq_tmp.point_paths_test" "" "2".
Fail elpi point_run_path "Unfolds to" "2".
Abort.

(* the notation actions (point_actions_notations.v): the line written,
   the line run, the goal printed after it *)
From coq_tmp Require Import point_actions_notations.
Goal forall a b : nat, a + b * 2 = b /\ forall n : nat, n * n = 0.
intros a b.
elpi point_run_path_expect "Disable notation" "Disable Notation := (Nat.mul _ _) (all)." "" "1.2.2".
(* under a binder *)
elpi point_run_path_expect "Disable notation" "Disable Notation := (Nat.mul _ _) (all)." "" "2.2.2".
Disable Notation := (Nat.mul _ _) (all).
elpi point_run_path_expect "Type of" "a + Nat.mul b 2 = b : Prop" "" "1".
Fail elpi point_run_path "Disable notation" "1.2.2".
elpi point_run_path_expect "Enable notation" "Enable Notation := (Nat.mul _ _) (all)." "" "1.2.2".
Enable Notation := (Nat.mul _ _) (all).
elpi point_run_path_expect "Type of" "a + b * 2 = b : Prop" "" "1".
Fail elpi point_run_path "Enable notation" "1.2.2".
(* eq's type is implicit: no _ for it; not covers ~ x and x <> y *)
elpi point_run_path_expect "Disable notation" "Disable Notation := (eq _ _) (all)." "" "1".
elpi point_run_path_expect "Without notations" "eq (Nat.add a (Nat.mul b 2)) b" "" "1".
elpi point_run_path_expect "Without notations" "Nat.mul n n" "" "2.2.2".
(* a variable, a product: no head *)
Fail elpi point_run_path "Disable notation" "1.2.1".
Fail elpi point_run_path "Disable notation" "2".
Abort.
