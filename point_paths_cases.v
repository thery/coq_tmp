(* The cases of the subterm paths: goals that cover every construct and
   every position of the numbering of the paths (pbp_select.v, kids;
   POINTING-PATHS.md), in the conclusion and in hypotheses.

   [elpi point_paths_check.] computes the text of every subterm and every
   binder name of the goal at that point (a native check: no error, the
   number of paths printed).  point_paths_roundtrip.sh, run with the Rocq
   whose printer tags the subterms with their paths (Set Printing Subterm
   Paths), replaces each [elpi point_paths_check.] by [Show.], reads the
   tags of the printed goal, and checks that for every tag P with text T
   the subterm (or the binder name) at path P prints as T. *)

From Stdlib Require Import ZArith String List.
From Stdlib Require ssreflect ssrbool Utf8.
From coq_tmp Require Import point_actions.

Definition double n := n + n.
Definition idn {A : Type} (n : nat) := n.
Definition add3 (a b c : nat) := a + b + c.

(* applications: the head (0), each argument (1, 2, ...), a partial
   application (add3 1 as an argument), a head that is an application
   (the result of a function), implicit arguments (idn's type, eq's type),
   @f explicit *)
Goal forall (f : nat -> nat -> nat) (g : nat -> nat -> nat),
  f 1 2 = double (f 2 1) /\ map (add3 1 2) (1 :: nil) = nil /\
  (if true then f else g) 3 4 = 0 /\ @idn bool 3 = @idn nat 3.
intros f g.
elpi point_paths_check.
Abort.

(* notations: infix (+, *, =, /\), prefix (~), mixfix (the IF one),
   Unicode (∀ ¬ ∧ ≤), scopes (%Z), numbers, strings, lists *)
Module Notations.
Notation "'IF' c 'THEN' a 'ELSE' b" := (if c then a else b) (at level 200).
Import ListNotations.
Goal forall (b : bool) (n : nat) (z : Z) (P Q : Prop),
  (IF b THEN n ELSE 0) = n * 2 /\ ~ (P /\ Q) /\ (z + 1 = 3)%Z /\
  ("ab c" ++ "d" = "ab cd")%string /\ [n; 1] ++ [] = n :: [1] /\
  (-3 + 12 = 9)%Z.
intros b n z P Q.
elpi point_paths_check.
Abort.
End Notations.

Module Unicode.
Import Utf8.
Goal ∀ α β : nat, α ≤ β → ¬ (β < α) ∧ (α = α ↔ True).
intros α β.
elpi point_paths_check.
Abort.
End Unicode.

(* ssreflect's notations: if-is, let:, [/\ ...] *)
Module S.
Import ssreflect ssrbool.
Goal forall (o : option nat) (p : nat * nat),
  (if o is Some n then n else 0) = (let: (a, b) := p in a + b) /\ [/\ true, true & ~~ false].
intros o p.
elpi point_paths_check.
Abort.
End S.

(* forall, fun, arrows: the name (0), the type (1), the body (2);
   grouped binders forall (a b : nat); dependent and non-dependent
   products; nested binders; exists and the other binder notations *)
Goal forall (a b : nat) (c : bool), bool -> (fun x y : nat => x + y) a b = a + b /\
  exists (u v : nat) (w : bool), u = v /\ w = c.
elpi point_paths_check.
intros a b c d.
elpi point_paths_check.
Abort.

Goal {n : nat | n > 0} -> {x : nat & x = x} -> exists m, m = 0.
elpi point_paths_check.
Abort.

(* let: the name (0), the type when it is printed (1), the value (2), the
   body (3); let '(a, b) := p, a match *)
Goal forall n : nat, (let m := n + 1 in m * m) = n /\ (let k : nat := 2 in k) = 2.
intros n.
elpi point_paths_check.
Abort.

Goal forall (p : nat * nat), (let '(a, b) := p in a + b) = 0.
intros p.
elpi point_paths_check.
Abort.

(* match: the scrutinee (0), the return clause (1), the branches (2, ...)
   with 0, 1, 2 bound names, a nested pattern S (S k), a wildcard;
   if/then/else; a return clause as x in T return P *)
Goal forall (n : nat) (l : list nat) (b : bool),
  match n with 0 => true | S (S k) => Nat.eqb k n | S _ => false end = true /\
  match l with nil => 0 | cons x r => x + length r end = 0 /\
  (if b then 1 else 0) = 1.
intros n l b.
elpi point_paths_check.
Abort.

Goal forall (b : bool), match b as x return (if x then nat else bool) with true => 0 | false => true end = match b as x return (if x then nat else bool) with true => 0 | false => true end.
intros b.
elpi point_paths_check.
Abort.

Inductive vec : nat -> Type := vnil : vec 0 | vcons : forall n, nat -> vec n -> vec (S n).
Goal forall (n : nat) (v : vec n), match v in vec m return nat with vnil => 0 | vcons k x _ => x + k end = 0.
intros n v.
elpi point_paths_check.
Abort.

(* casts *)
Goal forall n : nat, (n : nat) = n.
intros n.
change ((n : nat) = n).
elpi point_paths_check.
Abort.

(* coercions: hidden, then printed *)
Module C.
Coercion Z.of_nat : nat >-> Z.
Record box := Box { unbox :> nat }.
Goal forall (n : nat) (b : box), (n + 1 = b)%Z /\ b + 0 = n.
intros n b.
elpi point_paths_check.
Set Printing Coercions.
elpi point_paths_check.
Unset Printing Coercions.
Abort.
End C.

(* evars *)
Goal exists n : nat, n + 0 = 3.
eexists.
elpi point_paths_check.
Abort.

Goal forall m : nat, exists f : nat -> nat, f m = m.
intros m. eexists.
elpi point_paths_check.
Abort.

(* sorts, universes *)
Polymorphic Definition idT@{u} (A : Type@{u}) : Type@{u} := A.
Goal forall (A : Type) (P : Prop) (S : Set), idT A -> (P -> S -> Prop) -> Type.
intros A P S.
elpi point_paths_check.
Abort.

(* records and projections: primitive and not *)
Record pt := Pt { px : nat; py : nat }.
Goal forall p : pt, px p + py p = py (Pt (px p) 0) + px p.
intros p.
elpi point_paths_check.
Abort.

Set Primitive Projections.
Record ppt := PPt { qx : nat; qy : nat }.
Unset Primitive Projections.
Goal forall p : ppt, qx p = qy p.
intros p.
elpi point_paths_check.
Abort.

(* section variables, local definitions in the context *)
Section Sec.
Variable sv : nat.
Hypothesis sv_pos : sv > 0.
Goal sv + sv = 2 * sv -> sv > 0.
intros H.
pose (s := sv + 1).
elpi point_paths_check.
Abort.
End Sec.

(* hypotheses: binders, a match, a notation, a let in the type of a
   hypothesis *)
Goal forall n : nat, (forall k : nat, k + 0 = k) ->
  match n with 0 => True | S k => k = n end ->
  (let m := n in m = n) -> n = n.
intros n H1 H2 H3.
elpi point_paths_check.
Abort.

(* shadowed and renamed names: x and x0 *)
Goal forall x : nat, (forall x : nat, x = x) -> forall y, (fun x => x + y) x = x.
intros x H.
elpi point_paths_check.
Abort.

Goal forall x : nat, x = x -> forall x : nat, x = x.
elpi point_paths_check.
Abort.

(* Printing All *)
Set Printing All.
Goal forall a b : nat, a + b = b + a /\ (a <= b \/ True).
intros a b.
elpi point_paths_check.
Abort.
Unset Printing All.

(* a deep term, elided by Printing Depth *)
Set Printing Depth 4.
Goal forall a : nat, 1 + (2 + (3 + (4 + (5 + a)))) = a.
intros a.
elpi point_paths_check.
Abort.
Unset Printing Depth.
