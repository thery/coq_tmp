---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# Nat.lt_irrefl

Let `x : nat`{.var}. We prove `~ x < x`{.claim}.

- We have proved `(x ?= x) = Lt <-> x < x -> Basics.flip Basics.impl (~ x < x) ((x ?= x) <> Lt)`{.claim} (P1).
  - Assume `(x ?= x) = Lt <-> x < x`{.hyp} (lemma).
    - Applying subrelation_refl to iff, we have `RelationClasses.subrelation iff iff`{.claim} (P1.1).
      - The element `Prop`{.fact} belongs to `Type`{.fact}.
    - Applying subrelation_respectful to iff, iff, P1.1, iff and iff_flip_impl_subrelation, we have `RelationClasses.subrelation (Morphisms.respectful iff iff) (Morphisms.respectful iff (Basics.flip Basics.impl))`{.claim} (P1.2).
      - The element `Prop`{.fact} belongs to `Type`{.fact}.
      - The element `Prop`{.fact} belongs to `Type`{.fact}.
      - The element `Basics.flip Basics.impl`{.fact} belongs to `Relation_Definitions.relation Prop`{.fact}.
    - Applying subrelation_proper to not, not_iff_morphism, tt and P1.2, we have `Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) not`{.claim}, that is `forall x0 y : Prop, x0 <-> y -> Basics.flip Basics.impl (~ x0) (~ y)`{.fact} (P1.3).
      - The element `Prop -> Prop`{.fact} belongs to `Type`{.fact}.
      - The element `Morphisms.respectful iff iff`{.fact} belongs to `Relation_Definitions.relation (Prop -> Prop)`{.fact}.
      - The element `Morphisms.respectful iff (Basics.flip Basics.impl)`{.fact} belongs to `Relation_Definitions.relation (Prop -> Prop)`{.fact}.
    - Applying symmetry to iff, iff_Symmetric and lemma, we have `x < x <-> (x ?= x) = Lt`{.claim} (P1.4).
      - The element `Prop`{.fact} belongs to `Type`{.fact}.
      - The element `(x ?= x) = Lt`{.fact} belongs to `Prop`{.fact}.
      - The element `x < x`{.fact} belongs to `Prop`{.fact}.
    - The element `x < x`{.fact} belongs to `Prop`{.fact}.
    - The element `(x ?= x) = Lt`{.fact} belongs to `Prop`{.fact}.
    - Applying P1.3 to P1.4, we have `Basics.flip Basics.impl (~ x < x) ((x ?= x) <> Lt)`{.claim}.
- Applying compare_lt_iff to x and x, we have `(x ?= x) = Lt <-> x < x`{.claim} (P2).
- Applying P1 to P2, we have `Basics.flip Basics.impl (~ x < x) ((x ?= x) <> Lt)`{.claim}, that is `(x ?= x) <> Lt -> ~ x < x`{.fact} (P3).
- Rewriting with `(x ?= x) = Eq`{.fact} from right to left (eq_ind_r), we get `(x ?= x) <> Lt`{.claim}.
  - We have proved `Eq = Lt -> False`{.claim}.
    - Assume `Eq = Lt`{.hyp} (H).
      - Going back to the definition of eq (match) in `Eq = Lt`{.fact} (H), we prove `Lt = Lt -> False`{.claim}: (H0).
        - Assume `Eq = Lt`{.hyp} (H0).
          - Rewriting with `Eq = Lt`{.fact} from left to right (eq_ind), we get `match Lt with | Eq => True | _ => False end`{.claim} (H1).
            - By I we have `True`{.claim}.
            - By H0 we have `Eq = Lt`{.claim}.
          - By contradiction (False, False_ind), from `False`{.fact} (H1) we can deduce `False`{.claim}.
      - By definition of eq (eq_refl), we have `Lt = Lt`{.claim} *by Corelib.Init.Logic.eq_refl*.
      - Applying H0, we have `False`{.claim}.
  - Applying compare_refl to x, we have `(x ?= x) = Eq`{.claim}.
- Applying P3, we have `~ x < x`{.claim}.
