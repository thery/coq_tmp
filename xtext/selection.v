(* Tests of the selection of type annotations (Coscoy's thesis, 4.3.1,
   Fig. 4.10; elpi/staged.elpi, select): the annotated term of a theorem,
   printed as in the thesis, after the annotation (stage 1, with only the
   redundant double annotations made single, as in Fig. 4.23) and after
   the selection (Fig. 4.24).  Each test fails if a printed term is not
   the expected one. *)
From XText Require Import ExtractText thesis.
From XText Extra Dependency "test-helpers.elpi" as test_helpers.
Elpi Accumulate ExtractText File test_helpers.

(* [check-selection Name Annotated Selected] (for this file only) *)
Elpi Accumulate ExtractText lp:{{
  pred check-selection i:string, i:string, i:string.
  check-selection Name Annotated Selected :-
    with-switches (term-before-after Name A S),
    expect "annotated" Name Annotated A,
    expect "selected" Name Selected S.

  pred term-before-after i:string, o:string, o:string.
  term-before-after Name A S :-
    coq.locate Name (const C), coq.env.const C (some Bo) Ty,
    annotate Bo Ty T,
    contract "none" T T0, aterm-string T0 A,
    select T T1, aterm-string T1 S.
}}.


(* Fig. 4.23 and 4.24, the example ABCD.  Fig. 4.23 writes the
   applications with several arguments, without the types of the partial
   applications (h1 h4 : B -> C -> D); the annotation gives them.  The
   selected term is that of Fig. 4.24. *)
Elpi Query ExtractText lp:{{ check-selection "ABCD"
  "(λA:Prop. (λB:Prop. (λC:Prop. (λD:Prop. (λh1:A -> B -> C -> D. (λh2:A -> C -> B. (λh3:A -> C. (λh4:A. (((((((h1 : A -> B -> C -> D) (h4 : A)) : B -> C -> D) (((((h2 : A -> C -> B) (h4 : A)) : C -> B) (((h3 : A -> C) (h4 : A)) : C)) : B)) : C -> D) (((h3 : A -> C) (h4 : A)) : C)) : D) : A -> D) : (A -> C) -> A -> D) : (A -> C -> B) -> (A -> C) -> A -> D) : (A -> B -> C -> D) -> (A -> C -> B) -> (A -> C) -> A -> D) : forall D : Prop, (A -> B -> C -> D) -> (A -> C -> B) -> (A -> C) -> A -> D) : forall C D : Prop, (A -> B -> C -> D) -> (A -> C -> B) -> (A -> C) -> A -> D) : forall B C D : Prop, (A -> B -> C -> D) -> (A -> C -> B) -> (A -> C) -> A -> D) : forall A B C D : Prop, (A -> B -> C -> D) -> (A -> C -> B) -> (A -> C) -> A -> D)"
  "(λA:Prop. λB:Prop. λC:Prop. λD:Prop. λh1:A -> B -> C -> D. λh2:A -> C -> B. λh3:A -> C. λh4:A. ((h1 h4 ((h2 h4 ((h3 h4) : C)) : B) ((h3 h4) : C)) : D) : forall A B C D : Prop, (A -> B -> C -> D) -> (A -> C -> B) -> (A -> C) -> A -> D)" }}.

(* A conversion stays: in Trans_Inv (Fig. 3.10), h proves Trans E R and is
   used at its unfolding, h1 and h2 at R y x and R z y, the abstractions at
   Trans E (Inv E R).  The elements z, y, x (App2) lose their type. *)
Elpi Query ExtractText lp:{{ check-selection "Trans_Inv"
  "(λE:Set. (λR:Rel E. (λh:Trans E R. ((λx:E. (λy:E. (λz:E. (λh1:Inv E R x y. (λh2:Inv E R y z. (((((((((((((h : Trans E R) : forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0) (z : E)) : forall y0 z0 : E, R z y0 -> R y0 z0 -> R z z0) (y : E)) : forall z0 : E, R z y -> R y z0 -> R z z0) (x : E)) : R z y -> R y x -> R z x) ((h2 : Inv E R y z) : R z y)) : R y x -> R z x) ((h1 : Inv E R x y) : R y x)) : R z x) : Inv E R x z) : Inv E R y z -> Inv E R x z) : Inv E R x y -> Inv E R y z -> Inv E R x z) : forall z : E, Inv E R x y -> Inv E R y z -> Inv E R x z) : forall y z : E, Inv E R x y -> Inv E R y z -> Inv E R x z) : forall x y z : E, Inv E R x y -> Inv E R y z -> Inv E R x z) : Trans E (Inv E R)) : Trans E R -> Trans E (Inv E R)) : forall R : Rel E, Trans E R -> Trans E (Inv E R)) : forall (E : Set) (R : Rel E), Trans E R -> Trans E (Inv E R))"
  "(λE:Set. λR:Rel E. λh:Trans E R. ((λx:E. λy:E. λz:E. λh1:Inv E R x y. λh2:Inv E R y z. (((((h : Trans E R) : forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0) z y x ((h2 : Inv E R y z) : R z y) ((h1 : Inv E R x y) : R y x)) : R z x) : Inv E R x z) : forall x y z : E, Inv E R x y -> Inv E R y z -> Inv E R x z) : Trans E (Inv E R)) : forall (E : Set) (R : Rel E), Trans E R -> Trans E (Inv E R))" }}.

(* Fig. 4.11: one term per rule of Fig. 4.10 *)

(* Redundant type expressions: h is required to prove A and proves A *)
Definition rule_redundant : forall A : Prop, A -> A := fun A h => h.
Elpi Query ExtractText lp:{{ check-selection "rule_redundant"
  "(λA:Prop. (λh:A. (h : A) : A -> A) : forall A : Prop, A -> A)"
  "(λA:Prop. λh:A. (h : A) : forall A : Prop, A -> A)" }}.

(* Successive abstractions: forall x1 : T1, forall x2 : T2, T3 *)
Definition rule_abstractions : forall (T1 T2 T3 : Prop), T3 -> T1 -> T2 -> T3 :=
  fun T1 T2 T3 h x1 x2 => h.
Elpi Query ExtractText lp:{{ check-selection "rule_abstractions"
  "(λT1:Prop. (λT2:Prop. (λT3:Prop. (λh:T3. (λx1:T1. (λx2:T2. (h : T3) : T2 -> T3) : T1 -> T2 -> T3) : T3 -> T1 -> T2 -> T3) : forall T3 : Prop, T3 -> T1 -> T2 -> T3) : forall T2 T3 : Prop, T3 -> T1 -> T2 -> T3) : forall T1 T2 T3 : Prop, T3 -> T1 -> T2 -> T3)"
  "(λT1:Prop. λT2:Prop. λT3:Prop. λh:T3. λx1:T1. λx2:T2. (h : T3) : forall T1 T2 T3 : Prop, T3 -> T1 -> T2 -> T3)" }}.

(* Successive applications: T1 -> T2 -> T3 applied to proofs of T1 and T2
   that are not identifiers *)
Definition rule_applications :
  forall (T0 T1 T2 T3 : Prop), (T1 -> T2 -> T3) -> (T0 -> T1) -> (T0 -> T2) -> T0 -> T3 :=
  fun T0 T1 T2 T3 h f g a => h (f a) (g a).
Elpi Query ExtractText lp:{{ check-selection "rule_applications"
  "(λT0:Prop. (λT1:Prop. (λT2:Prop. (λT3:Prop. (λh:T1 -> T2 -> T3. (λf:T0 -> T1. (λg:T0 -> T2. (λa:T0. (((((h : T1 -> T2 -> T3) (((f : T0 -> T1) (a : T0)) : T1)) : T2 -> T3) (((g : T0 -> T2) (a : T0)) : T2)) : T3) : T0 -> T3) : (T0 -> T2) -> T0 -> T3) : (T0 -> T1) -> (T0 -> T2) -> T0 -> T3) : (T1 -> T2 -> T3) -> (T0 -> T1) -> (T0 -> T2) -> T0 -> T3) : forall T3 : Prop, (T1 -> T2 -> T3) -> (T0 -> T1) -> (T0 -> T2) -> T0 -> T3) : forall T2 T3 : Prop, (T1 -> T2 -> T3) -> (T0 -> T1) -> (T0 -> T2) -> T0 -> T3) : forall T1 T2 T3 : Prop, (T1 -> T2 -> T3) -> (T0 -> T1) -> (T0 -> T2) -> T0 -> T3) : forall T0 T1 T2 T3 : Prop, (T1 -> T2 -> T3) -> (T0 -> T1) -> (T0 -> T2) -> T0 -> T3)"
  "(λT0:Prop. λT1:Prop. λT2:Prop. λT3:Prop. λh:T1 -> T2 -> T3. λf:T0 -> T1. λg:T0 -> T2. λa:T0. ((h ((f a) : T1) ((g a) : T2)) : T3) : forall T0 T1 T2 T3 : Prop, (T1 -> T2 -> T3) -> (T0 -> T1) -> (T0 -> T2) -> T0 -> T3)" }}.

(* Argument of application: h, whose function is not an identifier *)
Definition rule_argument : forall (T1 T2 : Prop), (T2 -> T2 -> T1) -> T2 -> T1 :=
  fun T1 T2 k h => (fun x : T2 => k x x) h.
Elpi Query ExtractText lp:{{ check-selection "rule_argument"
  "(λT1:Prop. (λT2:Prop. (λk:T2 -> T2 -> T1. (λh:T2. (((λx:T2. (((((k : T2 -> T2 -> T1) (x : T2)) : T2 -> T1) (x : T2)) : T1) : T2 -> T1) (h : T2)) : T1) : T2 -> T1) : (T2 -> T2 -> T1) -> T2 -> T1) : forall T2 : Prop, (T2 -> T2 -> T1) -> T2 -> T1) : forall T1 T2 : Prop, (T2 -> T2 -> T1) -> T2 -> T1)"
  "(λT1:Prop. λT2:Prop. λk:T2 -> T2 -> T1. λh:T2. (((λx:T2. ((k x x) : T1) : T2 -> T1) h) : T1) : forall T1 T2 : Prop, (T2 -> T2 -> T1) -> T2 -> T1)" }}.

(* Head of application: h, whose argument is not an identifier *)
Definition rule_head : forall (T0 T1 T2 : Prop), (T2 -> T1) -> (T0 -> T2) -> T0 -> T1 :=
  fun T0 T1 T2 h g a => h (g a).
Elpi Query ExtractText lp:{{ check-selection "rule_head"
  "(λT0:Prop. (λT1:Prop. (λT2:Prop. (λh:T2 -> T1. (λg:T0 -> T2. (λa:T0. (((h : T2 -> T1) (((g : T0 -> T2) (a : T0)) : T2)) : T1) : T0 -> T1) : (T0 -> T2) -> T0 -> T1) : (T2 -> T1) -> (T0 -> T2) -> T0 -> T1) : forall T2 : Prop, (T2 -> T1) -> (T0 -> T2) -> T0 -> T1) : forall T1 T2 : Prop, (T2 -> T1) -> (T0 -> T2) -> T0 -> T1) : forall T0 T1 T2 : Prop, (T2 -> T1) -> (T0 -> T2) -> T0 -> T1)"
  "(λT0:Prop. λT1:Prop. λT2:Prop. λh:T2 -> T1. λg:T0 -> T2. λa:T0. ((h ((g a) : T2)) : T1) : forall T0 T1 T2 : Prop, (T2 -> T1) -> (T0 -> T2) -> T0 -> T1)" }}.
