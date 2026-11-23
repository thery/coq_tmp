---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# Nat.le_trans

Let `n m p : nat`{.var}. We prove `n <= m -> m <= p -> n <= p`{.claim}.

- In particular `n <= m <-> n < m \/ n = m`{.claim}.
  - Using *PeanoNat.Nat.lt_eq_cases*{.just} we get `forall n0 m0 : nat, n0 <= m0 <-> n0 < m0 \/ n0 = m0`{.claim}.
- In particular `m <= p <-> m < p \/ m = p`{.claim}.
  - Using *PeanoNat.Nat.lt_eq_cases*{.just} we get `forall n0 m0 : nat, n0 <= m0 <-> n0 < m0 \/ n0 = m0`{.claim}.
- We deduce `Basics.impl (n < m \/ n = m) (m < p \/ m = p -> n <= p)`{.claim}.
  - In particular `n <= p <-> n < p \/ n = p`{.claim}.
    - Using *PeanoNat.Nat.lt_eq_cases*{.just} we get `forall n0 m0 : nat, n0 <= m0 <-> n0 < m0 \/ n0 = m0`{.claim}.
  - By *lia*{.just} we have `n < m \/ n = m -> m < p \/ m = p -> n < p \/ n = p`, that is `Basics.impl (n < m \/ n = m) (m < p \/ m = p -> n < p \/ n = p)`{.claim}.
  - We have proved `n <= p <-> n < p \/ n = p -> Basics.flip Basics.impl (Basics.impl (n < m \/ n = m) (m < p \/ m = p -> n <= p)) (Basics.impl (n < m \/ n = m) (m < p \/ m = p -> n < p \/ n = p))`{.claim}.
    - Assume `n <= p <-> n < p \/ n = p`{.hyp} (lemma).
      - We deduce `Basics.impl (m < p \/ m = p) (n <= p) <-> Basics.impl (m < p \/ m = p) (n < p \/ n = p)`, that is `(m < p \/ m = p -> n <= p) <-> (m < p \/ m = p -> n < p \/ n = p)`{.claim}.
        - By *lemma*{.just} we have `n <= p <-> n < p \/ n = p`{.claim}.
        - We deduce `Morphisms.Proper (Morphisms.respectful iff iff) (Basics.impl (m < p \/ m = p))`, that is `forall x y : Prop, x <-> y -> Basics.impl (m < p \/ m = p) x <-> Basics.impl (m < p \/ m = p) y`{.claim}.
          - In particular `Morphisms.ProperProxy iff (m < p \/ m = p)`{.claim}.
            - We deduce `Morphisms.ReflexiveProxy iff`{.claim}.
              - Using *RelationClasses.iff_Reflexive*{.just} we get `RelationClasses.Reflexive iff`{.claim}.
              - Using *Morphisms.reflexive_reflexive_proxy*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> Morphisms.ReflexiveProxy R`{.claim}.
            - Using *Morphisms.reflexive_proper_proxy*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), Morphisms.ReflexiveProxy R -> forall x : A, Morphisms.ProperProxy R x`{.claim}.
            - We deduce `forall x : Prop, Morphisms.ProperProxy iff x`{.claim}.
          - We deduce `forall x : Prop, Morphisms.ProperProxy iff x -> Morphisms.Proper (Morphisms.respectful iff iff) (Basics.impl x)`{.claim}.
            - Using *Morphisms_Prop.iff_iff_iff_impl_morphism*{.just} we get `Morphisms.Proper (Morphisms.respectful iff (Morphisms.respectful iff iff)) Basics.impl`{.claim}.
            - Using *Morphisms.Reflexive_partial_app_morphism*{.just} we get `forall (A B : Type) (R : Relation_Definitions.relation A) (R' : Relation_Definitions.relation B) (m0 : A -> B), Morphisms.Proper (Morphisms.respectful R R') m0 -> forall x : A, Morphisms.ProperProxy R x -> Morphisms.Proper R' (m0 x)`{.claim}.
      - We deduce `Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (Basics.impl (n < m \/ n = m))`, that is `forall x y : Prop, x <-> y -> Basics.flip Basics.impl (Basics.impl (n < m \/ n = m) x) (Basics.impl (n < m \/ n = m) y)`{.claim}.
        - In particular `Morphisms.ProperProxy iff (n < m \/ n = m)`{.claim}.
          - We deduce `Morphisms.ReflexiveProxy iff`{.claim}.
            - Using *RelationClasses.iff_Reflexive*{.just} we get `RelationClasses.Reflexive iff`{.claim}.
            - Using *Morphisms.reflexive_reflexive_proxy*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> Morphisms.ReflexiveProxy R`{.claim}.
          - Using *Morphisms.reflexive_proper_proxy*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), Morphisms.ReflexiveProxy R -> forall x : A, Morphisms.ProperProxy R x`{.claim}.
          - We deduce `forall x : Prop, Morphisms.ProperProxy iff x`{.claim}.
        - We deduce `forall x : Prop, Morphisms.ProperProxy iff x -> Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (Basics.impl x)`{.claim}.
          - We deduce `Morphisms.Proper (Morphisms.respectful iff (Morphisms.respectful iff (Basics.flip Basics.impl))) Basics.impl`{.claim}.
            - We deduce `RelationClasses.subrelation (Morphisms.respectful iff (Morphisms.respectful iff iff)) (Morphisms.respectful iff (Morphisms.respectful iff (Basics.flip Basics.impl)))`{.claim}.
              - We deduce `RelationClasses.subrelation (Morphisms.respectful iff iff) (Morphisms.respectful iff (Basics.flip Basics.impl))`{.claim}.
                - Using *Morphisms.iff_flip_impl_subrelation*{.just} we get `RelationClasses.subrelation iff (Basics.flip Basics.impl)`{.claim}.
                - We deduce `forall RB RB' : Relation_Definitions.relation Prop, RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful iff RB) (Morphisms.respectful iff RB')`{.claim}.
                  - In particular `RelationClasses.subrelation iff iff`{.claim}.
                    - Using *Morphisms.subrelation_refl*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.subrelation R R`{.claim}.
                  - Using *Morphisms.subrelation_respectful*{.just} we get `forall (A B : Type) (RA' RA : Relation_Definitions.relation A), RelationClasses.subrelation RA' RA -> forall RB RB' : Relation_Definitions.relation B, RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful RA RB) (Morphisms.respectful RA' RB')`{.claim}.
              - We deduce `forall RB RB' : Relation_Definitions.relation (Prop -> Prop), RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful iff RB) (Morphisms.respectful iff RB')`{.claim}.
                - In particular `RelationClasses.subrelation iff iff`{.claim}.
                  - Using *Morphisms.subrelation_refl*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.subrelation R R`{.claim}.
                - Using *Morphisms.subrelation_respectful*{.just} we get `forall (A B : Type) (RA' RA : Relation_Definitions.relation A), RelationClasses.subrelation RA' RA -> forall RB RB' : Relation_Definitions.relation B, RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful RA RB) (Morphisms.respectful RA' RB')`{.claim}.
            - We deduce `forall R : Relation_Definitions.relation (Prop -> Prop -> Prop), Init.Unconvertible (Relation_Definitions.relation (Prop -> Prop -> Prop)) R (Morphisms.respectful iff (Morphisms.respectful iff iff)) -> RelationClasses.subrelation (Morphisms.respectful iff (Morphisms.respectful iff iff)) R -> Morphisms.Proper R Basics.impl`{.claim}.
              - Using *Morphisms_Prop.iff_iff_iff_impl_morphism*{.just} we get `Morphisms.Proper (Morphisms.respectful iff (Morphisms.respectful iff iff)) Basics.impl`{.claim}.
              - Using *Morphisms.subrelation_proper*{.just} we get `forall (A : Type) (R' : Relation_Definitions.relation A) (m0 : A), Morphisms.Proper R' m0 -> forall R : Relation_Definitions.relation A, Init.Unconvertible (Relation_Definitions.relation A) R R' -> RelationClasses.subrelation R' R -> Morphisms.Proper R m0`{.claim}.
          - Using *Morphisms.Reflexive_partial_app_morphism*{.just} we get `forall (A B : Type) (R : Relation_Definitions.relation A) (R' : Relation_Definitions.relation B) (m0 : A -> B), Morphisms.Proper (Morphisms.respectful R R') m0 -> forall x : A, Morphisms.ProperProxy R x -> Morphisms.Proper R' (m0 x)`{.claim}.

      We deduce `Basics.flip Basics.impl (Basics.impl (n < m \/ n = m) (m < p \/ m = p -> n <= p)) (Basics.impl (n < m \/ n = m) (m < p \/ m = p -> n < p \/ n = p))`{.claim}.
- We have proved `m <= p <-> m < p \/ m = p -> Basics.flip Basics.impl (Basics.impl (n < m \/ n = m) (m <= p -> n <= p)) (Basics.impl (n < m \/ n = m) (m < p \/ m = p -> n <= p))`{.claim}.
  - Assume `m <= p <-> m < p \/ m = p`{.hyp} (lemma).
    - We deduce `Basics.impl (m <= p) (n <= p) <-> Basics.impl (m < p \/ m = p) (n <= p)`, that is `(m <= p -> n <= p) <-> (m < p \/ m = p -> n <= p)`{.claim}.
      - In particular `Morphisms.ProperProxy iff (n <= p)`, that is `n <= p <-> n <= p`{.claim}.
        - We deduce `Morphisms.ReflexiveProxy iff`{.claim}.
          - Using *RelationClasses.iff_Reflexive*{.just} we get `RelationClasses.Reflexive iff`{.claim}.
          - Using *Morphisms.reflexive_reflexive_proxy*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> Morphisms.ReflexiveProxy R`{.claim}.
        - Using *Morphisms.reflexive_proper_proxy*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), Morphisms.ReflexiveProxy R -> forall x : A, Morphisms.ProperProxy R x`{.claim}.
        - We deduce `forall x : Prop, Morphisms.ProperProxy iff x`{.claim}.
      - We deduce `Morphisms.respectful iff iff (Basics.impl (m <= p)) (Basics.impl (m < p \/ m = p))`, that is `forall x y : Prop, x <-> y -> Basics.impl (m <= p) x <-> Basics.impl (m < p \/ m = p) y`{.claim}.
        - By *lemma*{.just} we have `m <= p <-> m < p \/ m = p`{.claim}.
        - Using *Morphisms_Prop.iff_iff_iff_impl_morphism*{.just} we get `Morphisms.Proper (Morphisms.respectful iff (Morphisms.respectful iff iff)) Basics.impl`, that is `forall x y : Prop, x <-> y -> Morphisms.respectful iff iff (Basics.impl x) (Basics.impl y)`{.claim}.
    - We deduce `Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (Basics.impl (n < m \/ n = m))`, that is `forall x y : Prop, x <-> y -> Basics.flip Basics.impl (Basics.impl (n < m \/ n = m) x) (Basics.impl (n < m \/ n = m) y)`{.claim}.
      - In particular `Morphisms.ProperProxy iff (n < m \/ n = m)`{.claim}.
        - We deduce `Morphisms.ReflexiveProxy iff`{.claim}.
          - Using *RelationClasses.iff_Reflexive*{.just} we get `RelationClasses.Reflexive iff`{.claim}.
          - Using *Morphisms.reflexive_reflexive_proxy*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> Morphisms.ReflexiveProxy R`{.claim}.
        - Using *Morphisms.reflexive_proper_proxy*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), Morphisms.ReflexiveProxy R -> forall x : A, Morphisms.ProperProxy R x`{.claim}.
        - We deduce `forall x : Prop, Morphisms.ProperProxy iff x`{.claim}.
      - We deduce `forall x : Prop, Morphisms.ProperProxy iff x -> Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (Basics.impl x)`{.claim}.
        - We deduce `Morphisms.Proper (Morphisms.respectful iff (Morphisms.respectful iff (Basics.flip Basics.impl))) Basics.impl`{.claim}.
          - We deduce `RelationClasses.subrelation (Morphisms.respectful iff (Morphisms.respectful iff iff)) (Morphisms.respectful iff (Morphisms.respectful iff (Basics.flip Basics.impl)))`{.claim}.
            - We deduce `RelationClasses.subrelation (Morphisms.respectful iff iff) (Morphisms.respectful iff (Basics.flip Basics.impl))`{.claim}.
              - Using *Morphisms.iff_flip_impl_subrelation*{.just} we get `RelationClasses.subrelation iff (Basics.flip Basics.impl)`{.claim}.
              - We deduce `forall RB RB' : Relation_Definitions.relation Prop, RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful iff RB) (Morphisms.respectful iff RB')`{.claim}.
                - In particular `RelationClasses.subrelation iff iff`{.claim}.
                  - Using *Morphisms.subrelation_refl*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.subrelation R R`{.claim}.
                - Using *Morphisms.subrelation_respectful*{.just} we get `forall (A B : Type) (RA' RA : Relation_Definitions.relation A), RelationClasses.subrelation RA' RA -> forall RB RB' : Relation_Definitions.relation B, RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful RA RB) (Morphisms.respectful RA' RB')`{.claim}.
            - We deduce `forall RB RB' : Relation_Definitions.relation (Prop -> Prop), RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful iff RB) (Morphisms.respectful iff RB')`{.claim}.
              - In particular `RelationClasses.subrelation iff iff`{.claim}.
                - Using *Morphisms.subrelation_refl*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.subrelation R R`{.claim}.
              - Using *Morphisms.subrelation_respectful*{.just} we get `forall (A B : Type) (RA' RA : Relation_Definitions.relation A), RelationClasses.subrelation RA' RA -> forall RB RB' : Relation_Definitions.relation B, RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful RA RB) (Morphisms.respectful RA' RB')`{.claim}.
          - We deduce `forall R : Relation_Definitions.relation (Prop -> Prop -> Prop), Init.Unconvertible (Relation_Definitions.relation (Prop -> Prop -> Prop)) R (Morphisms.respectful iff (Morphisms.respectful iff iff)) -> RelationClasses.subrelation (Morphisms.respectful iff (Morphisms.respectful iff iff)) R -> Morphisms.Proper R Basics.impl`{.claim}.
            - Using *Morphisms_Prop.iff_iff_iff_impl_morphism*{.just} we get `Morphisms.Proper (Morphisms.respectful iff (Morphisms.respectful iff iff)) Basics.impl`{.claim}.
            - Using *Morphisms.subrelation_proper*{.just} we get `forall (A : Type) (R' : Relation_Definitions.relation A) (m0 : A), Morphisms.Proper R' m0 -> forall R : Relation_Definitions.relation A, Init.Unconvertible (Relation_Definitions.relation A) R R' -> RelationClasses.subrelation R' R -> Morphisms.Proper R m0`{.claim}.
        - Using *Morphisms.Reflexive_partial_app_morphism*{.just} we get `forall (A B : Type) (R : Relation_Definitions.relation A) (R' : Relation_Definitions.relation B) (m0 : A -> B), Morphisms.Proper (Morphisms.respectful R R') m0 -> forall x : A, Morphisms.ProperProxy R x -> Morphisms.Proper R' (m0 x)`{.claim}.

    We deduce `Basics.flip Basics.impl (Basics.impl (n < m \/ n = m) (m <= p -> n <= p)) (Basics.impl (n < m \/ n = m) (m < p \/ m = p -> n <= p))`{.claim}.
- We have proved `n <= m <-> n < m \/ n = m -> Basics.flip Basics.impl (Basics.impl (n <= m) (m <= p -> n <= p)) (Basics.impl (n < m \/ n = m) (m <= p -> n <= p))`{.claim}.
  - Assume `n <= m <-> n < m \/ n = m`{.hyp} (lemma).
    - In particular `Morphisms.ProperProxy iff (m <= p -> n <= p)`, that is `(m <= p -> n <= p) <-> (m <= p -> n <= p)`{.claim}.
      - We deduce `Morphisms.ReflexiveProxy iff`{.claim}.
        - Using *RelationClasses.iff_Reflexive*{.just} we get `RelationClasses.Reflexive iff`{.claim}.
        - Using *Morphisms.reflexive_reflexive_proxy*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> Morphisms.ReflexiveProxy R`{.claim}.
      - Using *Morphisms.reflexive_proper_proxy*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), Morphisms.ReflexiveProxy R -> forall x : A, Morphisms.ProperProxy R x`{.claim}.
      - We deduce `forall x : Prop, Morphisms.ProperProxy iff x`{.claim}.
    - We deduce `Morphisms.respectful iff (Basics.flip Basics.impl) (Basics.impl (n <= m)) (Basics.impl (n < m \/ n = m))`, that is `forall x y : Prop, x <-> y -> Basics.flip Basics.impl (Basics.impl (n <= m) x) (Basics.impl (n < m \/ n = m) y)`{.claim}.
      - By *lemma*{.just} we have `n <= m <-> n < m \/ n = m`{.claim}.
      - We deduce `Morphisms.Proper (Morphisms.respectful iff (Morphisms.respectful iff (Basics.flip Basics.impl))) Basics.impl`, that is `forall x y : Prop, x <-> y -> Morphisms.respectful iff (Basics.flip Basics.impl) (Basics.impl x) (Basics.impl y)`{.claim}.
        - We deduce `RelationClasses.subrelation (Morphisms.respectful iff (Morphisms.respectful iff iff)) (Morphisms.respectful iff (Morphisms.respectful iff (Basics.flip Basics.impl)))`{.claim}.
          - We deduce `RelationClasses.subrelation (Morphisms.respectful iff iff) (Morphisms.respectful iff (Basics.flip Basics.impl))`{.claim}.
            - Using *Morphisms.iff_flip_impl_subrelation*{.just} we get `RelationClasses.subrelation iff (Basics.flip Basics.impl)`{.claim}.
            - We deduce `forall RB RB' : Relation_Definitions.relation Prop, RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful iff RB) (Morphisms.respectful iff RB')`{.claim}.
              - In particular `RelationClasses.subrelation iff iff`{.claim}.
                - Using *Morphisms.subrelation_refl*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.subrelation R R`{.claim}.
              - Using *Morphisms.subrelation_respectful*{.just} we get `forall (A B : Type) (RA' RA : Relation_Definitions.relation A), RelationClasses.subrelation RA' RA -> forall RB RB' : Relation_Definitions.relation B, RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful RA RB) (Morphisms.respectful RA' RB')`{.claim}.
          - We deduce `forall RB RB' : Relation_Definitions.relation (Prop -> Prop), RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful iff RB) (Morphisms.respectful iff RB')`{.claim}.
            - In particular `RelationClasses.subrelation iff iff`{.claim}.
              - Using *Morphisms.subrelation_refl*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.subrelation R R`{.claim}.
            - Using *Morphisms.subrelation_respectful*{.just} we get `forall (A B : Type) (RA' RA : Relation_Definitions.relation A), RelationClasses.subrelation RA' RA -> forall RB RB' : Relation_Definitions.relation B, RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful RA RB) (Morphisms.respectful RA' RB')`{.claim}.
        - We deduce `forall R : Relation_Definitions.relation (Prop -> Prop -> Prop), Init.Unconvertible (Relation_Definitions.relation (Prop -> Prop -> Prop)) R (Morphisms.respectful iff (Morphisms.respectful iff iff)) -> RelationClasses.subrelation (Morphisms.respectful iff (Morphisms.respectful iff iff)) R -> Morphisms.Proper R Basics.impl`{.claim}.
          - Using *Morphisms_Prop.iff_iff_iff_impl_morphism*{.just} we get `Morphisms.Proper (Morphisms.respectful iff (Morphisms.respectful iff iff)) Basics.impl`{.claim}.
          - Using *Morphisms.subrelation_proper*{.just} we get `forall (A : Type) (R' : Relation_Definitions.relation A) (m0 : A), Morphisms.Proper R' m0 -> forall R : Relation_Definitions.relation A, Init.Unconvertible (Relation_Definitions.relation A) R R' -> RelationClasses.subrelation R' R -> Morphisms.Proper R m0`{.claim}.

    We deduce `Basics.flip Basics.impl (Basics.impl (n <= m) (m <= p -> n <= p)) (Basics.impl (n < m \/ n = m) (m <= p -> n <= p))`{.claim}.
- By *tauto*{.just} we deduce `Basics.impl (n <= m) (m <= p -> n <= p)`, that is `n <= m -> m <= p -> n <= p`{.claim}.
