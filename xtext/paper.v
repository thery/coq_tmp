(* The examples of "Extracting Text from Proofs" (TLCA 1995), as Rocq terms.
   They end with Defined or Qed: both work, Explain reads opaque bodies. *)
From Stdlib Require Import Arith.
From XText Require Import Explain.

(* Section 3.1, "Type information": the identity *)
Definition identity : forall A : Prop, A -> A := fun A h => h.
Explain identity to "examples/identity.md".

(* Section 3.1, the proof (S) *)
Definition S_proof : forall A B C : Prop, (A -> B -> C) -> (A -> B) -> A -> C :=
  fun A B C h h0 h1 => h h1 (h0 h1).
Explain S_proof to "examples/S_proof.md".

(* "Introduction theorems" *)
Definition or_intro_example : forall A B C : Prop, A -> B \/ (A \/ C) :=
  fun A B C h => or_intror (or_introl h).
Explain or_intro_example to "examples/or_intro_example.md".

(* "Elimination theorems": commutativity of the disjunction *)
Definition or_commut : forall A B : Prop, A \/ B -> B \/ A :=
  fun A B h => or_ind (fun i : A => or_intror i) (fun j : B => or_introl j) h.
Explain or_commut to "examples/or_commut.md".

(* "Elimination theorems": a proof by induction *)
Definition le_0_m : forall m : nat, 0 <= m :=
  nat_ind (fun x => 0 <= x) (le_n 0) (fun m (h : 0 <= m) => le_S 0 m h).
Explain le_0_m to "examples/le_0_m.md".

(* Figure "Three examples": praeclarum *)
Definition praeclarum : forall x y z t : Prop,
  (x -> z) /\ (y -> t) -> x /\ y -> z /\ t :=
  fun x y z t h1 h2 =>
    and_ind (fun (i : x -> z) (j : y -> t) =>
      and_ind (fun (k : x) (l : y) => conj (i k) (j l)) h2) h1.
Explain praeclarum to "examples/praeclarum.md".

(* Figure "Three examples": a symmetric and transitive relation is nearly
   reflexive *)
Definition nearly_reflexive : forall (A : Set) (R : A -> A -> Prop),
  (forall x y : A, R x y -> R y x) ->
  (forall x y z : A, R x y -> R y z -> R x z) ->
  forall x : A, (exists y0 : A, R x y0) -> R x x :=
  fun A R symmetry transitivity x h =>
    ex_ind (fun (y0 : A) (i : R x y0) =>
              transitivity x y0 x i (symmetry x y0 i)) h.
Explain nearly_reflexive to "examples/nearly_reflexive.md".

(* Figure "Three examples": the drinker's principle (classical) *)
From Stdlib Require Import Classical.
Lemma drinker (A : Set) (P : A -> Prop) (y : A) :
  exists x : A, P x -> forall z : A, P z.
Proof.
  destruct (classic (forall z : A, P z)) as [H|H].
  - exists y. intros _. exact H.
  - destruct (not_all_ex_not A P H) as [t i].
    exists t. intros h. destruct (i h).
Qed.
Explain drinker to "examples/drinker.md".
