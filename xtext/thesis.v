(* The four running examples of Coscoy's thesis (Nice, 2000), with proof
   terms as close as possible to the thesis's lambda-terms. *)
From XText Require Import Explain.

(* Tauto (Fig. 1.4, 1.5, 2.6, 2.8, 2.11) *)
Definition Tauto : forall A B C : Prop, A -> B -> (A -> B -> C) -> C :=
  fun A B C h1 h2 h3 => h3 h1 h2.
Time Explain Tauto to "examples/Tauto.md".

(* Trans_Inv (Fig. 3.5-3.13) *)
Definition Rel (E : Set) := E -> E -> Prop.
Definition Trans (E : Set) (R : Rel E) :=
  forall x y z : E, R x y -> R y z -> R x z.
Definition Inv (E : Set) (R : Rel E) : Rel E := fun x y => R y x.
Definition Trans_Inv : forall (E : Set) (R : Rel E), Trans E R -> Trans E (Inv E R) :=
  fun E R h x y z (h1 : Inv E R x y) (h2 : Inv E R y z) => h z y x h2 h1.
Time Explain Trans_Inv to "examples/Trans_Inv.md".

(* the example of chapters 4 and 5 (Fig. 4.28, 5.5, 5.6) *)
Definition ABCD : forall A B C D : Prop,
  (A -> B -> C -> D) -> (A -> C -> B) -> (A -> C) -> A -> D :=
  fun A B C D h1 h2 h3 h4 => h1 h4 (h2 h4 (h3 h4)) (h3 h4).
Time Explain ABCD to "examples/ABCD.md".

(* or_com (Fig. 6.2, 6.3, 6.5) *)
Definition or_com : forall A B : Prop, A \/ B -> B \/ A :=
  fun A B H =>
    or_ind (fun H0 : A => or_intror H0) (fun H0 : B => or_introl H0) H.
Time Explain or_com to "examples/or_com.md".

(* Examples of L. Théry's thesis (1994), chapter 3 and 4 *)

(* a \/ b -> b \/ a (Fig. 3.3): or-elimination with two cases *)
Definition or_sym_nd : forall a b : Prop, a \/ b -> b \/ a :=
  fun a b (H1 : a \/ b) =>
    match H1 with
    | or_introl H2 => or_intror H2
    | or_intror H3 => or_introl H3
    end.
Time Explain or_sym_nd to "examples/or_sym_nd.md".

(* praeclarum (section 3.3.3), with the and-eliminations of natural
   deduction (proj1, proj2) *)
Definition praeclarum_nd : forall x y z t : Prop,
  (x -> z) /\ (y -> t) -> x /\ y -> z /\ t :=
  fun x y z t H1 H2 =>
    conj (proj1 H1 (proj1 H2)) (proj2 H1 (proj2 H2)).
Time Explain praeclarum_nd to "examples/praeclarum_nd.md".

(* ADD0 (section 4.9.2): forall m, m + 0 = m by induction *)
Definition ADD0 : forall m : nat, m + 0 = m :=
  fun m => nat_ind (fun m => m + 0 = m) eq_refl
             (fun m (IH : m + 0 = m) => f_equal S IH) m.
Time Explain ADD0 to "examples/ADD0.md".
