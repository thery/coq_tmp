---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# Nat.lt_irrefl

Let `x : nat`{.var}. We prove `~ x < x`{.claim}.

- By application, we have `Basics.flip Basics.impl (~ x < x) ((x ?= x) <> Lt)`, that is `(x ?= x) <> Lt -> ~ x < x`{.claim}.
  - We have proved `(x ?= x) = Lt <-> x < x -> Basics.flip Basics.impl (~ x < x) ((x ?= x) <> Lt)`{.claim}.
    - Assume `(x ?= x) = Lt <-> x < x`{.hyp} (lemma).
      - By application, we have `x < x <-> (x ?= x) = Lt -> Basics.flip Basics.impl (~ x < x) ((x ?= x) <> Lt)`{.claim}.
        - By application, we have `forall y : Prop, x < x <-> y -> Basics.flip Basics.impl (~ x < x) (~ y)`{.claim}.
          - By application, we have `Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) not`, that is `forall x0 y : Prop, x0 <-> y -> Basics.flip Basics.impl (~ x0) (~ y)`{.claim}.
            - By application, we have `RelationClasses.subrelation (Morphisms.respectful iff iff) (Morphisms.respectful iff (Basics.flip Basics.impl)) -> Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) not`{.claim}.
              - By application, we have `Init.Unconvertible (Relation_Definitions.relation (Prop -> Prop)) (Morphisms.respectful iff (Basics.flip Basics.impl)) (Morphisms.respectful iff iff) -> RelationClasses.subrelation (Morphisms.respectful iff iff) (Morphisms.respectful iff (Basics.flip Basics.impl)) -> Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) not`{.claim}.
                - By application, we have `forall R : Relation_Definitions.relation (Prop -> Prop), Init.Unconvertible (Relation_Definitions.relation (Prop -> Prop)) R (Morphisms.respectful iff iff) -> RelationClasses.subrelation (Morphisms.respectful iff iff) R -> Morphisms.Proper R not`{.claim}.
                  - By application, we have `Morphisms.Proper (Morphisms.respectful iff iff) not -> forall R : Relation_Definitions.relation (Prop -> Prop), Init.Unconvertible (Relation_Definitions.relation (Prop -> Prop)) R (Morphisms.respectful iff iff) -> RelationClasses.subrelation (Morphisms.respectful iff iff) R -> Morphisms.Proper R not`{.claim}.
                    - By application, we have `forall m : Prop -> Prop, Morphisms.Proper (Morphisms.respectful iff iff) m -> forall R : Relation_Definitions.relation (Prop -> Prop), Init.Unconvertible (Relation_Definitions.relation (Prop -> Prop)) R (Morphisms.respectful iff iff) -> RelationClasses.subrelation (Morphisms.respectful iff iff) R -> Morphisms.Proper R m`{.claim}.
                      - By application, we have `forall (R' : Relation_Definitions.relation (Prop -> Prop)) (m : Prop -> Prop), Morphisms.Proper R' m -> forall R : Relation_Definitions.relation (Prop -> Prop), Init.Unconvertible (Relation_Definitions.relation (Prop -> Prop)) R R' -> RelationClasses.subrelation R' R -> Morphisms.Proper R m`{.claim}.
                        - By *Morphisms.subrelation_proper*{.just} we have `forall (A : Type) (R' : Relation_Definitions.relation A) (m : A), Morphisms.Proper R' m -> forall R : Relation_Definitions.relation A, Init.Unconvertible (Relation_Definitions.relation A) R R' -> RelationClasses.subrelation R' R -> Morphisms.Proper R m`{.claim}.
                        - The element `Prop -> Prop` belongs to `Type`.
                      - The element `Morphisms.respectful iff iff` belongs to `Relation_Definitions.relation (Prop -> Prop)`.
                    - The element `not` belongs to `Prop -> Prop`.
                  - By *Morphisms_Prop.not_iff_morphism*{.just} we have `Morphisms.Proper (Morphisms.respectful iff iff) not`{.claim}.
                - The element `Morphisms.respectful iff (Basics.flip Basics.impl)` belongs to `Relation_Definitions.relation (Prop -> Prop)`.
              - The element `tt` belongs to `Init.Unconvertible (Relation_Definitions.relation (Prop -> Prop)) (Morphisms.respectful iff (Basics.flip Basics.impl)) (Morphisms.respectful iff iff)`.
            - By application, we have `RelationClasses.subrelation (Morphisms.respectful iff iff) (Morphisms.respectful iff (Basics.flip Basics.impl))`{.claim}.
              - By application, we have `RelationClasses.subrelation iff (Basics.flip Basics.impl) -> RelationClasses.subrelation (Morphisms.respectful iff iff) (Morphisms.respectful iff (Basics.flip Basics.impl))`{.claim}.
                - By application, we have `forall RB' : Relation_Definitions.relation Prop, RelationClasses.subrelation iff RB' -> RelationClasses.subrelation (Morphisms.respectful iff iff) (Morphisms.respectful iff RB')`{.claim}.
                  - By application, we have `forall RB RB' : Relation_Definitions.relation Prop, RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful iff RB) (Morphisms.respectful iff RB')`{.claim}.
                    - By application, we have `RelationClasses.subrelation iff iff -> forall RB RB' : Relation_Definitions.relation Prop, RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful iff RB) (Morphisms.respectful iff RB')`{.claim}.
                      - By application, we have `forall RA : Relation_Definitions.relation Prop, RelationClasses.subrelation iff RA -> forall RB RB' : Relation_Definitions.relation Prop, RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful RA RB) (Morphisms.respectful iff RB')`{.claim}.
                        - By application, we have `forall RA' RA : Relation_Definitions.relation Prop, RelationClasses.subrelation RA' RA -> forall RB RB' : Relation_Definitions.relation Prop, RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful RA RB) (Morphisms.respectful RA' RB')`{.claim}.
                          - By application, we have `forall (B : Type) (RA' RA : Relation_Definitions.relation Prop), RelationClasses.subrelation RA' RA -> forall RB RB' : Relation_Definitions.relation B, RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful RA RB) (Morphisms.respectful RA' RB')`{.claim}.
                            - By *Morphisms.subrelation_respectful*{.just} we have `forall (A B : Type) (RA' RA : Relation_Definitions.relation A), RelationClasses.subrelation RA' RA -> forall RB RB' : Relation_Definitions.relation B, RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful RA RB) (Morphisms.respectful RA' RB')`{.claim}.
                            - The element `Prop` belongs to `Type`.
                          - The element `Prop` belongs to `Type`.
                        - The element `iff` belongs to `Relation_Definitions.relation Prop`.
                      - The element `iff` belongs to `Relation_Definitions.relation Prop`.
                    - By application, we have `RelationClasses.subrelation iff iff`{.claim}.
                      - By application, we have `forall R : Relation_Definitions.relation Prop, RelationClasses.subrelation R R`{.claim}.
                        - By *Morphisms.subrelation_refl*{.just} we have `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.subrelation R R`{.claim}.
                        - The element `Prop` belongs to `Type`.
                      - The element `iff` belongs to `Relation_Definitions.relation Prop`.
                  - The element `iff` belongs to `Relation_Definitions.relation Prop`.
                - The element `Basics.flip Basics.impl` belongs to `Relation_Definitions.relation Prop`.
              - By *Morphisms.iff_flip_impl_subrelation*{.just} we have `RelationClasses.subrelation iff (Basics.flip Basics.impl)`{.claim}.
          - The element `x < x` belongs to `Prop`.
        - The element `(x ?= x) = Lt` belongs to `Prop`.
      - By application, we have `x < x <-> (x ?= x) = Lt`{.claim}.
        - By application, we have `(x ?= x) = Lt <-> x < x -> x < x <-> (x ?= x) = Lt`{.claim}.
          - By application, we have `forall y : Prop, (x ?= x) = Lt <-> y -> y <-> (x ?= x) = Lt`{.claim}.
            - By application, we have `forall x0 y : Prop, x0 <-> y -> y <-> x0`{.claim}.
              - By application, we have `RelationClasses.Symmetric iff -> forall x0 y : Prop, x0 <-> y -> y <-> x0`{.claim}.
                - By application, we have `forall R : Relation_Definitions.relation Prop, RelationClasses.Symmetric R -> forall x0 y : Prop, R x0 y -> R y x0`{.claim}.
                  - By *RelationClasses.symmetry*{.just} we have `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Symmetric R -> forall x0 y : A, R x0 y -> R y x0`{.claim}.
                  - The element `Prop` belongs to `Type`.
                - The element `iff` belongs to `Relation_Definitions.relation Prop`.
              - By *RelationClasses.iff_Symmetric*{.just} we have `RelationClasses.Symmetric iff`{.claim}.
            - The element `(x ?= x) = Lt` belongs to `Prop`.
          - The element `x < x` belongs to `Prop`.
        - By *lemma*{.just} we have `(x ?= x) = Lt <-> x < x`{.claim}.

      By application, we have `Basics.flip Basics.impl (~ x < x) ((x ?= x) <> Lt)`{.claim}.
  - By application, we have `(x ?= x) = Lt <-> x < x`{.claim}.
    - By application, we have `forall m : nat, (x ?= m) = Lt <-> x < m`{.claim}.
      - By *PeanoNat.Nat.compare_lt_iff*{.just} we have `forall n m : nat, (n ?= m) = Lt <-> n < m`{.claim}.
- Rewriting with `(x ?= x) = Eq`{.fact} from right to left (eq_ind_r), we get `(x ?= x) <> Lt`{.claim}.
  - We have proved `Eq = Lt -> False`{.claim}.
    - Assume `Eq = Lt`{.hyp} (H).
      - Going back to the definition of eq (match) in *H*{.just}, we prove `Lt = Lt -> False`{.claim} (H0):
        - Assume `Eq = Lt`{.hyp} (H0).
          - Rewriting with `Eq = Lt`{.fact} from left to right (eq_ind), we get `match Lt with | Eq => True | _ => False end`{.claim} (H1).
            - By *I*{.just} we have `True`{.claim}.
            - By *H0*{.just} we have `Eq = Lt`{.claim}.

          By contradiction (False, *False_ind*{.just}), from *H1*{.just} we can deduce `False`{.claim}.
      - By *H0*{.just} we have `Lt = Lt -> False`{.claim}.
      - By definition of eq (*eq_refl*{.just}), we have `Lt = Lt`{.claim}.

      By application, we have `False`{.claim}.
  - By application, we have `(x ?= x) = Eq`{.claim}.
    - By *PeanoNat.Nat.compare_refl*{.just} we have `forall x0 : nat, (x0 ?= x0) = Eq`{.claim}.
- By application, we have `~ x < x`{.claim}.
