---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# Nat.mul_1_r

Let `n : nat`{.var}. We prove `n * 1 = n`{.claim}.

- We have proved `1 = 1 -> Basics.flip Basics.impl (n * 1 = n) (n * 1 = n)`{.claim}.
  - Assume `1 = 1`{.hyp} (lemma).
    - The element `nat` belongs to `Type`.
    - The element `eq` belongs to `Relation_Definitions.relation nat`.
    - Applying *RelationClasses.Equivalence_Transitive*{.just}, we have `RelationClasses.Transitive (@eq nat)`{.claim}.
      - The element `nat` belongs to `Type`.
      - The element `eq` belongs to `Relation_Definitions.relation nat`.
      - By *PeanoNat.Nat.eq_equiv*{.just} we have `RelationClasses.Equivalence (@eq nat)`{.claim}.
    - The element `n * 1` belongs to `nat`.
    - The element `n * 1` belongs to `nat`.
    - Applying *Morphisms.Reflexive_partial_app_morphism*{.just}, we have `n * 1 = n * 1`{.claim}.
      - The element `nat` belongs to `Type`.
      - The element `nat -> nat` belongs to `Type`.
      - The element `eq` belongs to `Relation_Definitions.relation nat`.
      - The element `Morphisms.respectful eq eq` belongs to `Relation_Definitions.relation (nat -> nat)`.
      - The element `Nat.mul` belongs to `nat -> nat -> nat`.
      - By *PeanoNat.Nat.mul_wd*{.just} we have `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Nat.mul`{.claim}.
      - Applying *Morphisms.reflexive_proper_proxy*{.just}, we have `Morphisms.ProperProxy eq n`{.claim}.
        - The element `nat` belongs to `Type`.
        - The element `eq` belongs to `Relation_Definitions.relation nat`.
        - Applying *Morphisms.reflexive_reflexive_proxy*{.just}, we have `Morphisms.ReflexiveProxy (@eq nat)`{.claim}.
          - The element `nat` belongs to `Type`.
          - The element `eq` belongs to `Relation_Definitions.relation nat`.
          - Applying *RelationClasses.Equivalence_Reflexive*{.just}, we have `RelationClasses.Reflexive (@eq nat)`{.claim}.
            - The element `nat` belongs to `Type`.
            - The element `eq` belongs to `Relation_Definitions.relation nat`.
            - By *PeanoNat.Nat.eq_equiv*{.just} we have `RelationClasses.Equivalence (@eq nat)`{.claim}.
      - The element `1` belongs to `nat`.
      - The element `1` belongs to `nat`.
      - By *lemma*{.just} we have `1 = 1`{.claim}.
    - Applying *Morphisms.eq_proper_proxy*{.just} to nat and n, we have `Morphisms.ProperProxy eq n`, that is `n = n`{.claim}.

    Applying *Morphisms.trans_co_eq_inv_impl_morphism*{.just}, we have `Basics.flip Basics.impl (n * 1 = n) (n * 1 = n)`{.claim}.
- By *PeanoNat.Nat.one_succ*{.just} we have `1 = 1`{.claim}.
- By application, we have `n * 1 = n`{.claim}.
  - We have proved `n * 1 = n * 0 + n -> Basics.flip Basics.impl (n * 1 = n) (n * 0 + n = n)`{.claim}.
    - Assume `n * 1 = n * 0 + n`{.hyp} (lemma).
      - The element `nat` belongs to `Type`.
      - The element `eq` belongs to `Relation_Definitions.relation nat`.
      - Applying *RelationClasses.Equivalence_Transitive*{.just}, we have `RelationClasses.Transitive (@eq nat)`{.claim}.
        - The element `nat` belongs to `Type`.
        - The element `eq` belongs to `Relation_Definitions.relation nat`.
        - By *PeanoNat.Nat.eq_equiv*{.just} we have `RelationClasses.Equivalence (@eq nat)`{.claim}.
      - The element `n * 1` belongs to `nat`.
      - The element `n * 0 + n` belongs to `nat`.
      - By *lemma*{.just} we have `n * 1 = n * 0 + n`{.claim}.
      - Applying *Morphisms.eq_proper_proxy*{.just} to nat and n, we have `Morphisms.ProperProxy eq n`, that is `n = n`{.claim}.

      Applying *Morphisms.trans_co_eq_inv_impl_morphism*{.just}, we have `Basics.flip Basics.impl (n * 1 = n) (n * 0 + n = n)`{.claim}.
  - Applying *PeanoNat.Nat.mul_succ_r*{.just} to n and O, we have `n * 1 = n * 0 + n`{.claim}.
  - By application, we have `n * 0 + n = n`{.claim}.
    - We have proved `n * 0 = 0 -> Basics.flip Basics.impl (n * 0 + n = n) (0 + n = n)`{.claim}.
      - Assume `n * 0 = 0`{.hyp} (lemma).
        - The element `nat` belongs to `Type`.
        - The element `eq` belongs to `Relation_Definitions.relation nat`.
        - Applying *RelationClasses.Equivalence_Transitive*{.just}, we have `RelationClasses.Transitive (@eq nat)`{.claim}.
          - The element `nat` belongs to `Type`.
          - The element `eq` belongs to `Relation_Definitions.relation nat`.
          - By *PeanoNat.Nat.eq_equiv*{.just} we have `RelationClasses.Equivalence (@eq nat)`{.claim}.
        - The element `n * 0 + n` belongs to `nat`.
        - The element `0 + n` belongs to `nat`.
        - Applying *PeanoNat.Nat.add_wd*{.just}, we have `n * 0 + n = 0 + n`{.claim}.
          - The element `n * 0` belongs to `nat`.
          - The element `0` belongs to `nat`.
          - By *lemma*{.just} we have `n * 0 = 0`{.claim}.
          - Applying *Morphisms.reflexive_proper_proxy*{.just}, we have `Morphisms.ProperProxy eq n`, that is `n = n`{.claim}.
            - The element `nat` belongs to `Type`.
            - The element `eq` belongs to `Relation_Definitions.relation nat`.
            - Applying *Morphisms.reflexive_reflexive_proxy*{.just}, we have `Morphisms.ReflexiveProxy (@eq nat)`{.claim}.
              - The element `nat` belongs to `Type`.
              - The element `eq` belongs to `Relation_Definitions.relation nat`.
              - Applying *RelationClasses.Equivalence_Reflexive*{.just}, we have `RelationClasses.Reflexive (@eq nat)`{.claim}.
                - The element `nat` belongs to `Type`.
                - The element `eq` belongs to `Relation_Definitions.relation nat`.
                - By *PeanoNat.Nat.eq_equiv*{.just} we have `RelationClasses.Equivalence (@eq nat)`{.claim}.
        - Applying *Morphisms.eq_proper_proxy*{.just} to nat and n, we have `Morphisms.ProperProxy eq n`, that is `n = n`{.claim}.

        Applying *Morphisms.trans_co_eq_inv_impl_morphism*{.just}, we have `Basics.flip Basics.impl (n * 0 + n = n) (0 + n = n)`{.claim}.
    - Applying *PeanoNat.Nat.mul_0_r*{.just} to n, we have `n * 0 = 0`{.claim}.
    - By application, we have `0 + n = n`{.claim}.
      - We have proved `0 + n = n -> Basics.flip Basics.impl (0 + n = n) (n = n)`{.claim}.
        - Assume `0 + n = n`{.hyp} (lemma).
          - The element `nat` belongs to `Type`.
          - The element `eq` belongs to `Relation_Definitions.relation nat`.
          - Applying *RelationClasses.Equivalence_Transitive*{.just}, we have `RelationClasses.Transitive (@eq nat)`{.claim}.
            - The element `nat` belongs to `Type`.
            - The element `eq` belongs to `Relation_Definitions.relation nat`.
            - By *PeanoNat.Nat.eq_equiv*{.just} we have `RelationClasses.Equivalence (@eq nat)`{.claim}.
          - The element `0 + n` belongs to `nat`.
          - By *lemma*{.just} we have `0 + n = n`{.claim}.
          - Applying *Morphisms.eq_proper_proxy*{.just} to nat and n, we have `Morphisms.ProperProxy eq n`, that is `n = n`{.claim}.

          Applying *Morphisms.trans_co_eq_inv_impl_morphism*{.just}, we have `Basics.flip Basics.impl (0 + n = n) (n = n)`{.claim}.
      - Applying *PeanoNat.Nat.add_0_l*{.just} to n, we have `0 + n = n`{.claim}.
      - Applying *RelationClasses.reflexivity*{.just}, we have `n = n`{.claim}.
        - The element `nat` belongs to `Type`.
        - The element `eq` belongs to `Relation_Definitions.relation nat`.
        - Applying *RelationClasses.Equivalence_Reflexive*{.just}, we have `RelationClasses.Reflexive (@eq nat)`{.claim}.
          - The element `nat` belongs to `Type`.
          - The element `eq` belongs to `Relation_Definitions.relation nat`.
          - By *PeanoNat.Nat.eq_equiv*{.just} we have `RelationClasses.Equivalence (@eq nat)`{.claim}.
- By application, we have `n * 1 = n`{.claim}.
