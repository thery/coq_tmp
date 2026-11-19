---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# Nat.lt_irrefl

Let `x : nat`{.var}. We prove `~ x < x`{.claim}.

- Using *PeanoNat.Nat.compare_lt_iff*{.just} we get `forall n m : nat, (n ?= m) = Lt <-> n < m`{.claim}.
- Rewriting with `(x ?= x) = Eq`{.fact} from right to left (eq_ind_r), we get `(x ?= x) <> Lt`{.claim}.
  - We have proved `Eq = Lt -> False`{.claim}.
    - Assume `Eq = Lt`{.hyp} (H).
      - Going back to the definition of eq (match) in *H*{.just}, we prove `Lt = Lt -> False`{.claim} (H0):
        - Assume `Eq = Lt`{.hyp} (H0).
          - Rewriting with `Eq = Lt`{.fact} from left to right (eq_ind), we get `match Lt with | Eq => True | _ => False end`{.claim} (H1).
            - By definition of True (*I*{.just}), we have `True`{.claim}.
            - By *H0*{.just} we have `Eq = Lt`{.claim}.

          By contradiction (False, *False_ind*{.just}), from *H1*{.just} we can deduce `False`{.claim}.
      - By definition of eq (*eq_refl*{.just}), we have `Lt = Lt`{.claim}.
      - By *H0*{.just} we have `Lt = Lt -> False`{.claim}.

      We deduce `False`{.claim}.
  - In particular `(x ?= x) = Eq`{.claim}.
    - Using *PeanoNat.Nat.compare_refl*{.just} we get `forall x0 : nat, (x0 ?= x0) = Eq`{.claim}.
- We have proved `(x ?= x) = Lt <-> x < x -> Basics.flip Basics.impl (~ x < x) ((x ?= x) <> Lt)`{.claim}.
  - Assume `(x ?= x) = Lt <-> x < x`{.hyp} (lemma).
    - By *lemma*{.just} we have `(x ?= x) = Lt <-> x < x`{.claim}.
    - Using *RelationClasses.iff_Symmetric*{.just} we get `RelationClasses.Symmetric iff`{.claim}.
    - Using *RelationClasses.symmetry*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Symmetric R -> forall x0 y : A, R x0 y -> R y x0`{.claim}.
    - We deduce `Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) not`, that is `forall x0 y : Prop, x0 <-> y -> Basics.flip Basics.impl (~ x0) (~ y)`{.claim}.
      - We deduce `RelationClasses.subrelation (Morphisms.respectful iff iff) (Morphisms.respectful iff (Basics.flip Basics.impl))`{.claim}.
        - Using *Morphisms.iff_flip_impl_subrelation*{.just} we get `RelationClasses.subrelation iff (Basics.flip Basics.impl)`{.claim}.
        - We deduce `forall RB RB' : Relation_Definitions.relation Prop, RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful iff RB) (Morphisms.respectful iff RB')`{.claim}.
          - In particular `RelationClasses.subrelation iff iff`{.claim}.
            - Using *Morphisms.subrelation_refl*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.subrelation R R`{.claim}.
          - Using *Morphisms.subrelation_respectful*{.just} we get `forall (A B : Type) (RA' RA : Relation_Definitions.relation A), RelationClasses.subrelation RA' RA -> forall RB RB' : Relation_Definitions.relation B, RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful RA RB) (Morphisms.respectful RA' RB')`{.claim}.
      - We deduce `forall R : Relation_Definitions.relation (Prop -> Prop), Init.Unconvertible (Relation_Definitions.relation (Prop -> Prop)) R (Morphisms.respectful iff iff) -> RelationClasses.subrelation (Morphisms.respectful iff iff) R -> Morphisms.Proper R not`{.claim}.
        - Using *Morphisms_Prop.not_iff_morphism*{.just} we get `Morphisms.Proper (Morphisms.respectful iff iff) not`{.claim}.
        - Using *Morphisms.subrelation_proper*{.just} we get `forall (A : Type) (R' : Relation_Definitions.relation A) (m : A), Morphisms.Proper R' m -> forall R : Relation_Definitions.relation A, Init.Unconvertible (Relation_Definitions.relation A) R R' -> RelationClasses.subrelation R' R -> Morphisms.Proper R m`{.claim}.

    By *firstorder*{.just} we deduce `Basics.flip Basics.impl (~ x < x) ((x ?= x) <> Lt)`{.claim}.
- By *lia*{.just} we deduce `~ x < x`{.claim}.
