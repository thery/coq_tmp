---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# Nat.lt_irrefl

Let `x : nat`{.var}. We prove `~ x < x`{.claim}.

- By application, we have `Basics.flip Basics.impl (~ x < x) ((x ?= x) <> Lt)`, that is `(x ?= x) <> Lt -> ~ x < x`{.claim}.
  - We have proved `(x ?= x) = Lt <-> x < x -> Basics.flip Basics.impl (~ x < x) ((x ?= x) <> Lt)`{.claim}.
    - Assume `(x ?= x) = Lt <-> x < x`{.hyp} (lemma).
      - Applying *Morphisms.subrelation_proper*{.just}, we have `Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) not`, that is `forall x0 y : Prop, x0 <-> y -> Basics.flip Basics.impl (~ x0) (~ y)`{.claim}.
        - The element `Prop -> Prop` belongs to `Type`.
        - The element `Morphisms.respectful iff iff` belongs to `Relation_Definitions.relation (Prop -> Prop)`.
        - The element `not` belongs to `Prop -> Prop`.
        - By *Morphisms_Prop.not_iff_morphism*{.just} we have `Morphisms.Proper (Morphisms.respectful iff iff) not`{.claim}.
        - The element `Morphisms.respectful iff (Basics.flip Basics.impl)` belongs to `Relation_Definitions.relation (Prop -> Prop)`.
        - The element `tt` belongs to `Init.Unconvertible (Relation_Definitions.relation (Prop -> Prop)) (Morphisms.respectful iff (Basics.flip Basics.impl)) (Morphisms.respectful iff iff)`.
        - Applying *Morphisms.subrelation_respectful*{.just}, we have `RelationClasses.subrelation (Morphisms.respectful iff iff) (Morphisms.respectful iff (Basics.flip Basics.impl))`{.claim}.
          - The element `Prop` belongs to `Type`.
          - The element `Prop` belongs to `Type`.
          - The element `iff` belongs to `Relation_Definitions.relation Prop`.
          - The element `iff` belongs to `Relation_Definitions.relation Prop`.
          - Applying *Morphisms.subrelation_refl*{.just}, we have `RelationClasses.subrelation iff iff`{.claim}.
            - The element `Prop` belongs to `Type`.
            - The element `iff` belongs to `Relation_Definitions.relation Prop`.
          - The element `iff` belongs to `Relation_Definitions.relation Prop`.
          - The element `Basics.flip Basics.impl` belongs to `Relation_Definitions.relation Prop`.
          - By *Morphisms.iff_flip_impl_subrelation*{.just} we have `RelationClasses.subrelation iff (Basics.flip Basics.impl)`{.claim}.
      - The element `x < x` belongs to `Prop`.
      - The element `(x ?= x) = Lt` belongs to `Prop`.
      - Applying *RelationClasses.symmetry*{.just}, we have `x < x <-> (x ?= x) = Lt`{.claim}.
        - The element `Prop` belongs to `Type`.
        - The element `iff` belongs to `Relation_Definitions.relation Prop`.
        - By *RelationClasses.iff_Symmetric*{.just} we have `RelationClasses.Symmetric iff`{.claim}.
        - The element `(x ?= x) = Lt` belongs to `Prop`.
        - The element `x < x` belongs to `Prop`.
        - By *lemma*{.just} we have `(x ?= x) = Lt <-> x < x`{.claim}.

      By application, we have `Basics.flip Basics.impl (~ x < x) ((x ?= x) <> Lt)`{.claim}.
  - Applying *PeanoNat.Nat.compare_lt_iff*{.just} to x and x, we have `(x ?= x) = Lt <-> x < x`{.claim}.
- Rewriting with `(x ?= x) = Eq`{.fact} from right to left (eq_ind_r), we get `(x ?= x) <> Lt`{.claim}.
  - We have proved `Eq = Lt -> False`{.claim}.
    - Assume `Eq = Lt`{.hyp} (H).
      - Going back to the definition of eq (match) in *H*{.just}, we prove `Lt = Lt -> False`{.claim} (H0):
        - Assume `Eq = Lt`{.hyp} (H0).
          - Rewriting with `Eq = Lt`{.fact} from left to right (eq_ind), we get `match Lt with | Eq => True | _ => False end`{.claim} (H1).
            - By *I*{.just} we have `True`{.claim}.
            - By *H0*{.just} we have `Eq = Lt`{.claim}.

          By contradiction (False, *False_ind*{.just}), from *H1*{.just} we can deduce `False`{.claim}.
      - By definition of eq (*eq_refl*{.just}), we have `Lt = Lt`{.claim}.

      Applying *H0*{.just}, we have `False`{.claim}.
  - Applying *PeanoNat.Nat.compare_refl*{.just} to x, we have `(x ?= x) = Eq`{.claim}.
- By application, we have `~ x < x`{.claim}.
