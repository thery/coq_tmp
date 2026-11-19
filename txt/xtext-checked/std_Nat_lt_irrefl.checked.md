---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# Nat.lt_irrefl

✅ Let `x : nat`{.var}. We prove `~ x < x`{.claim}.

- ✅ By application, we have `Basics.flip Basics.impl (~ x < x) ((x ?= x) <> Lt)`{.claim}, that is `(x ?= x) <> Lt -> ~ x < x`{.fact}.
  - ✅ We have proved `(x ?= x) = Lt <-> x < x -> Basics.flip Basics.impl (~ x < x) ((x ?= x) <> Lt)`{.claim}.
    - ▫️ Assume `(x ?= x) = Lt <-> x < x`{.hyp} (lemma).
      - ✅ Applying subrelation_proper, we have `Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) not`{.claim}, that is `forall x0 y : Prop, x0 <-> y -> Basics.flip Basics.impl (~ x0) (~ y)`{.fact}.
        - ▫️ The element `Prop -> Prop`{.fact} belongs to `Type`{.fact}.
        - ▫️ The element `Morphisms.respectful iff iff`{.fact} belongs to `Relation_Definitions.relation (Prop -> Prop)`{.fact}.
        - ▫️ The element `not`{.fact} belongs to `Prop -> Prop`{.fact}.
        - ✅ By not_iff_morphism we have `Morphisms.Proper (Morphisms.respectful iff iff) not`{.claim}.
        - ▫️ The element `Morphisms.respectful iff (Basics.flip Basics.impl)`{.fact} belongs to `Relation_Definitions.relation (Prop -> Prop)`{.fact}.
        - ▫️ The element `tt`{.fact} belongs to `Init.Unconvertible (Relation_Definitions.relation (Prop -> Prop)) (Morphisms.respectful iff (Basics.flip Basics.impl)) (Morphisms.respectful iff iff)`{.fact}.
        - ❌ Applying subrelation_respectful, we have `RelationClasses.subrelation (Morphisms.respectful iff iff) (Morphisms.respectful iff (Basics.flip Basics.impl))`{.claim}.

          <details><summary>not proved: RelationClasses.subrelation (Morphisms.respectful iff iff)
  (Morphisms.respectful iff (Basics.flip Basics.impl))</summary></details>

          - ▫️ The element `Prop`{.fact} belongs to `Type`{.fact}.
          - ▫️ The element `Prop`{.fact} belongs to `Type`{.fact}.
          - ▫️ The element `iff`{.fact} belongs to `Relation_Definitions.relation Prop`{.fact}.
          - ▫️ The element `iff`{.fact} belongs to `Relation_Definitions.relation Prop`{.fact}.
          - ✅ Applying subrelation_refl, we have `RelationClasses.subrelation iff iff`{.claim}.
            - ▫️ The element `Prop`{.fact} belongs to `Type`{.fact}.
            - ▫️ The element `iff`{.fact} belongs to `Relation_Definitions.relation Prop`{.fact}.
          - ▫️ The element `iff`{.fact} belongs to `Relation_Definitions.relation Prop`{.fact}.
          - ▫️ The element `Basics.flip Basics.impl`{.fact} belongs to `Relation_Definitions.relation Prop`{.fact}.
          - ✅ By iff_flip_impl_subrelation we have `RelationClasses.subrelation iff (Basics.flip Basics.impl)`{.claim}.
      - ▫️ The element `x < x`{.fact} belongs to `Prop`{.fact}.
      - ▫️ The element `(x ?= x) = Lt`{.fact} belongs to `Prop`{.fact}.
      - ✅ Applying symmetry, we have `x < x <-> (x ?= x) = Lt`{.claim}.
        - ▫️ The element `Prop`{.fact} belongs to `Type`{.fact}.
        - ▫️ The element `iff`{.fact} belongs to `Relation_Definitions.relation Prop`{.fact}.
        - ✅ By iff_Symmetric we have `RelationClasses.Symmetric iff`{.claim}.
        - ▫️ The element `(x ?= x) = Lt`{.fact} belongs to `Prop`{.fact}.
        - ▫️ The element `x < x`{.fact} belongs to `Prop`{.fact}.
        - ✅ By lemma we have `(x ?= x) = Lt <-> x < x`{.claim}.
      - ✅ By application, we have `Basics.flip Basics.impl (~ x < x) ((x ?= x) <> Lt)`{.claim}.
  - ❌ Applying compare_lt_iff to x and x, we have `(x ?= x) = Lt <-> x < x`{.claim}.

    <details><summary>not proved: (x ?= x) = Lt <-> x < x</summary></details>

- ✅ Rewriting with `(x ?= x) = Eq`{.fact} from right to left (eq_ind_r), we get `(x ?= x) <> Lt`{.claim}.
  - ✅ We have proved `Eq = Lt -> False`{.claim}.
    - ▫️ Assume `Eq = Lt`{.hyp} (H).
      - ✅ Going back to the definition of eq (match) in `Eq = Lt`{.fact} (H), we prove `Lt = Lt -> False`{.claim}: (H0).
        - ▫️ Assume `Eq = Lt`{.hyp} (H0).
          - ✅ Rewriting with `Eq = Lt`{.fact} from left to right (eq_ind), we get `match Lt with | Eq => True | _ => False end`{.claim} (H1).
            - ✅ By I we have `True`{.claim}.
            - ✅ By H0 we have `Eq = Lt`{.claim}.
          - ✅ By contradiction (False, False_ind), from `False`{.fact} (H1) we can deduce `False`{.claim}.
      - ✅ By definition of eq (eq_refl), we have `Lt = Lt`{.claim} *by Corelib.Init.Logic.eq_refl*.
      - ✅ Applying H0, we have `False`{.claim}.
  - ❌ Applying compare_refl to x, we have `(x ?= x) = Eq`{.claim}.

    <details><summary>not proved: (x ?= x) = Eq</summary></details>

- ✅ By application, we have `~ x < x`{.claim}.
