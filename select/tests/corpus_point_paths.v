(* Differential corpus: the goals of point_paths_test.v, with every pattern
   that select_all and point_to_pattern produce for every path.  Run by
   run.sh. *)
From Stdlib Require Import String.
From elpi Require Import elpi.
From coq_tmp.select.tests Require Import diff_support.

Definition double n := n + n.

Goal forall a : nat, 1 + 1 + a = double (1 + a).
intros a.
elpi diff_gen "pp.1".
Abort.

Goal forall a b : nat, a = b -> b = a.
intros a b ab.
elpi diff_gen "pp.2".
Abort.

Goal ("a b" = "a b")%string.
elpi diff_gen "pp.3".
Abort.

Goal forall (p : nat * nat), (let '(a, b) := p in a + b) = 0 -> True.
intros p H.
elpi diff_gen "pp.4".
Abort.

Goal forall (n : nat) (b : bool), match n with 0 => true | S k => Nat.eqb k n end = (if b then false else true).
intros n b.
elpi diff_gen "pp.5".
Abort.

Goal forall (b : bool), match b as x return (if x then nat else bool) with true => 0 | false => true end = match b as x return (if x then nat else bool) with true => 0 | false => true end.
intros b.
elpi diff_gen "pp.6".
Abort.

Goal forall x : nat, (forall x : nat, x = x) -> forall y, (fun x => x + y) x = x.
intros x H.
elpi diff_gen "pp.7".
Abort.

Goal forall (a b : nat) (c d : bool), (fun x y : nat => x + y) a b = a + b /\ exists (u v : nat) (w : bool), u = v /\ w = c.
elpi diff_gen "pp.8".
Abort.

Goal forall n : nat, (n : nat) = n.
intros n.
change ((n : nat) = n).
elpi diff_gen "pp.9".
Abort.

Module C.
From Stdlib Require Import ZArith.
Coercion Z.of_nat : nat >-> Z.
Record box := Box { unbox :> nat }.
Goal forall (n : nat) (b : box), (n + 1 = b)%Z /\ b + 0 = n.
intros n b.
elpi diff_gen "pp.10".
Abort.
End C.

Set Printing All.
Goal forall a b : nat, a + b = b + a /\ (a <= b \/ True).
intros a b.
elpi diff_gen "pp.11".
Abort.
Unset Printing All.

Goal forall n : nat, n = n.
intros n.
elpi diff_gen "pp.12".
Abort.

Module IfMatch.
Notation "'IF' c 'THEN' a 'ELSE' b" := (if c then a else b) (at level 200).
Goal forall (b : bool) (n : nat), (IF b THEN n ELSE 0) = n.
intros b n.
elpi diff_gen "pp.13".
Abort.
End IfMatch.

Goal forall (b : bool) (n : nat), (if b then n else 0) = n.
intros b n.
elpi diff_gen "pp.14".
Abort.

Goal forall n : nat, match n with 0 => true | S _ => false end = true.
intros n.
elpi diff_gen "pp.15".
Abort.

Goal forall n : nat, n + 0 = n.
elpi diff_gen "pp.16".
Abort.

Goal forall n : nat, (let m := n + 1 in m * m) = n /\ (fun k : nat => k) n = n.
intros n.
elpi diff_gen "pp.17".
Abort.

Goal forall (n : nat), match n with 0 => true | S k => Nat.eqb k n end = true -> (forall z : nat, z = z) -> True.
intros n H H'.
elpi diff_gen "pp.18".
Abort.

Lemma two_is : 2 = 1 + 1. Proof. reflexivity. Qed.
Goal forall a : nat, double (1 + a) = 2 + a + a -> forall n : nat, n + double a = a.
intros a H.
elpi diff_gen "pp.19".
Abort.

Goal forall a : nat, (if true then a else 0) = double 2.
intros a.
elpi diff_gen "pp.20".
Abort.

Goal two_is = two_is.
elpi diff_gen "pp.21".
Abort.

Goal forall a b : nat, a + b * 2 = b /\ forall n : nat, n * n = 0.
intros a b.
elpi diff_gen "pp.22".
Abort.

Goal (exists m : nat, m = 0) /\ True.
elpi diff_gen "pp.23".
Abort.
