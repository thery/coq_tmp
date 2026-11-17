---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# Nat.lt_irrefl

Let `x : nat`{.var}. We prove `~ x < x`{.claim}.

- In particular `(x ?= x) = Lt <-> x < x`{.claim}.
  - Using compare_lt_iff we get `forall n m : nat, (n ?= m) = Lt <-> n < m`{.claim} *by exact @compare_lt_iff*.
- Rewriting with `(x ?= x) = Eq`{.fact} from right to left (eq_ind_r), we get `(x ?= x) <> Lt`{.claim}.
  - We have proved `Eq = Lt -> False`{.claim}.
    - Assume `Eq = Lt`{.hyp} (H).
      - Going back to the definition of eq (match) in `Eq = Lt`{.fact} (H), we prove `Lt = Lt -> False`{.claim}: (H0).
        - Assume `Eq = Lt`{.hyp} (H0).
          - Rewriting with `Eq = Lt`{.fact} from left to right (eq_ind), we get `match Lt with | Eq => True | _ => False end`{.claim} (H1).
            - By definition of True (I), we have `True`{.claim} *by eapply @I; eauto*.
            - By H0 we have `Eq = Lt`{.claim}.
          - By contradiction (False, False_ind), from `False`{.fact} (H1) we can deduce `False`{.claim}.
      - By definition of eq (eq_refl), we have `Lt = Lt`{.claim} *by eapply @eq_refl; eauto*.
      - By H0 we have `Lt = Lt -> False`{.claim}.
      - We deduce `False`{.claim}.
  - In particular `(x ?= x) = Eq`{.claim}.
    - Using compare_refl we get `forall x0 : nat, (x0 ?= x0) = Eq`{.claim} *by exact @compare_refl*.
- We have proved `(x ?= x) = Lt <-> x < x -> Basics.flip Basics.impl (~ x < x) ((x ?= x) <> Lt)`{.claim}.
  - Assume `(x ?= x) = Lt <-> x < x`{.hyp} (lemma).
    - We deduce `x < x <-> (x ?= x) = Lt`{.claim}.
      - By lemma we have `(x ?= x) = Lt <-> x < x`{.claim}.
      - In particular `(x ?= x) = Lt <-> x < x -> x < x <-> (x ?= x) = Lt`{.claim}.
        - Using iff_Symmetric we get `RelationClasses.Symmetric iff`{.claim} *by exact @iff_Symmetric*.
        - In particular `RelationClasses.Symmetric iff -> forall x0 y : Prop, x0 <-> y -> y <-> x0`{.claim}.
          - Using symmetry we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Symmetric R -> forall x0 y : A, R x0 y -> R y x0`{.claim} *by exact @symmetry*.
        - We deduce `forall x0 y : Prop, x0 <-> y -> y <-> x0`{.claim}.
    - In particular `x < x <-> (x ?= x) = Lt -> Basics.flip Basics.impl (~ x < x) ((x ?= x) <> Lt)`{.claim}.
      - We deduce `RelationClasses.subrelation (Morphisms.respectful iff iff) (Morphisms.respectful iff (Basics.flip Basics.impl))`{.claim}.
        - Using iff_flip_impl_subrelation we get `RelationClasses.subrelation iff (Basics.flip Basics.impl)`{.claim} *by exact @iff_flip_impl_subrelation*.
        - In particular `RelationClasses.subrelation iff (Basics.flip Basics.impl) -> RelationClasses.subrelation (Morphisms.respectful iff iff) (Morphisms.respectful iff (Basics.flip Basics.impl))`{.claim}.
          - In particular `RelationClasses.subrelation iff iff`{.claim}.
            - Using subrelation_refl we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.subrelation R R`{.claim} *by exact @subrelation_refl*.
          - In particular `RelationClasses.subrelation iff iff -> forall RB RB' : Relation_Definitions.relation Prop, RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful iff RB) (Morphisms.respectful iff RB')`{.claim}.
            - Using subrelation_respectful we get `forall (A B : Type) (RA' RA : Relation_Definitions.relation A), RelationClasses.subrelation RA' RA -> forall RB RB' : Relation_Definitions.relation B, RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful RA RB) (Morphisms.respectful RA' RB')`{.claim} *by exact @subrelation_respectful*.
          - We deduce `forall RB RB' : Relation_Definitions.relation Prop, RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful iff RB) (Morphisms.respectful iff RB')`{.claim}.
      - In particular `RelationClasses.subrelation (Morphisms.respectful iff iff) (Morphisms.respectful iff (Basics.flip Basics.impl)) -> Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) not`{.claim}.
        - Using not_iff_morphism we get `Morphisms.Proper (Morphisms.respectful iff iff) not`{.claim} *by exact @not_iff_morphism*.
        - In particular `Morphisms.Proper (Morphisms.respectful iff iff) not -> forall R : Relation_Definitions.relation (Prop -> Prop), Init.Unconvertible (Relation_Definitions.relation (Prop -> Prop)) R (Morphisms.respectful iff iff) -> RelationClasses.subrelation (Morphisms.respectful iff iff) R -> Morphisms.Proper R not`{.claim}.
          - Using subrelation_proper we get `forall (A : Type) (R' : Relation_Definitions.relation A) (m : A), Morphisms.Proper R' m -> forall R : Relation_Definitions.relation A, Init.Unconvertible (Relation_Definitions.relation A) R R' -> RelationClasses.subrelation R' R -> Morphisms.Proper R m`{.claim} *by exact @subrelation_proper*.
        - We deduce `forall R : Relation_Definitions.relation (Prop -> Prop), Init.Unconvertible (Relation_Definitions.relation (Prop -> Prop)) R (Morphisms.respectful iff iff) -> RelationClasses.subrelation (Morphisms.respectful iff iff) R -> Morphisms.Proper R not`{.claim}.
      - We deduce `Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) not`{.claim}.
    - We deduce `Basics.flip Basics.impl (~ x < x) ((x ?= x) <> Lt)`{.claim}.
- We deduce `~ x < x`{.claim}.
