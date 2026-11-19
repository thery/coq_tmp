---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# Nat.mul_1_r

Let `n : nat`{.var}. We prove `n * 1 = n`{.claim}.

- By application, with *PeanoNat.Nat.one_succ*{.just}, we have `Basics.flip Basics.impl (n * 1 = n) (n * 1 = n)`, that is `n * 1 = n -> n * 1 = n`{.claim}.
  - We have proved `1 = 1 -> Basics.flip Basics.impl (n * 1 = n) (n * 1 = n)`{.claim}.
    - Assume `1 = 1`{.hyp} (lemma).
      - By application, we have `Morphisms.respectful eq (Basics.flip Basics.impl) (eq (n * 1)) (eq (n * 1))`, that is `forall x y : nat, x = y -> Basics.flip Basics.impl (n * 1 = x) (n * 1 = y)`{.claim}.
        - Applying *Morphisms.trans_co_eq_inv_impl_morphism*{.just} to nat, we have `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq (Basics.flip Basics.impl))) (@eq nat)`, that is `forall x y : nat, x = y -> Morphisms.respectful eq (Basics.flip Basics.impl) (eq x) (eq y)`{.claim}.
          - The element `eq` belongs to `Relation_Definitions.relation nat`.
          - Applying *RelationClasses.Equivalence_Transitive*{.just} to nat and *PeanoNat.Nat.eq_equiv*{.just}, we have `RelationClasses.Transitive (@eq nat)`{.claim}.
            - The element `eq` belongs to `Relation_Definitions.relation nat`.
        - The element `n * 1` belongs to `nat`.
        - The element `n * 1` belongs to `nat`.
        - By application, with *lemma*{.just}, we have `n * 1 = n * 1`{.claim}.
          - Applying *Morphisms.Reflexive_partial_app_morphism*{.just} to nat, Nat.mul, *PeanoNat.Nat.mul_wd*{.just} and n, we have `Morphisms.Proper (Morphisms.respectful eq eq) (Nat.mul n)`, that is `forall x y : nat, x = y -> n * x = n * y`{.claim}.
            - The element `nat -> nat` belongs to `Type`.
            - The element `eq` belongs to `Relation_Definitions.relation nat`.
            - The element `Morphisms.respectful eq eq` belongs to `Relation_Definitions.relation (nat -> nat)`.
            - Applying *Morphisms.reflexive_proper_proxy*{.just} to nat and n, we have `Morphisms.ProperProxy eq n`{.claim}.
              - The element `eq` belongs to `Relation_Definitions.relation nat`.
              - Applying *Morphisms.reflexive_reflexive_proxy*{.just} to nat, we have `Morphisms.ReflexiveProxy (@eq nat)`{.claim}.
                - The element `eq` belongs to `Relation_Definitions.relation nat`.
                - Applying *RelationClasses.Equivalence_Reflexive*{.just} to nat and *PeanoNat.Nat.eq_equiv*{.just}, we have `RelationClasses.Reflexive (@eq nat)`{.claim}.
                  - The element `eq` belongs to `Relation_Definitions.relation nat`.
          - The element `1` belongs to `nat`.
          - The element `1` belongs to `nat`.
      - Applying *Morphisms.eq_proper_proxy*{.just} to nat and n, we have `Morphisms.ProperProxy eq n`, that is `n = n`{.claim}.

      By application, with n and n, we have `Basics.flip Basics.impl (n * 1 = n) (n * 1 = n)`{.claim}.
- By application, we have `n * 1 = n`{.claim}.
  - By application, we have `Basics.flip Basics.impl (n * 1 = n) (n * 0 + n = n)`, that is `n * 0 + n = n -> n * 1 = n`{.claim}.
    - We have proved `n * 1 = n * 0 + n -> Basics.flip Basics.impl (n * 1 = n) (n * 0 + n = n)`{.claim}.
      - Assume `n * 1 = n * 0 + n`{.hyp} (lemma).
        - By application, with *lemma*{.just}, we have `Morphisms.respectful eq (Basics.flip Basics.impl) (eq (n * 1)) (eq (n * 0 + n))`, that is `forall x y : nat, x = y -> Basics.flip Basics.impl (n * 1 = x) (n * 0 + n = y)`{.claim}.
          - Applying *Morphisms.trans_co_eq_inv_impl_morphism*{.just} to nat, we have `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq (Basics.flip Basics.impl))) (@eq nat)`, that is `forall x y : nat, x = y -> Morphisms.respectful eq (Basics.flip Basics.impl) (eq x) (eq y)`{.claim}.
            - The element `eq` belongs to `Relation_Definitions.relation nat`.
            - Applying *RelationClasses.Equivalence_Transitive*{.just} to nat and *PeanoNat.Nat.eq_equiv*{.just}, we have `RelationClasses.Transitive (@eq nat)`{.claim}.
              - The element `eq` belongs to `Relation_Definitions.relation nat`.
          - The element `n * 1` belongs to `nat`.
          - The element `n * 0 + n` belongs to `nat`.
        - Applying *Morphisms.eq_proper_proxy*{.just} to nat and n, we have `Morphisms.ProperProxy eq n`, that is `n = n`{.claim}.

        By application, with n and n, we have `Basics.flip Basics.impl (n * 1 = n) (n * 0 + n = n)`{.claim}.
    - Applying *PeanoNat.Nat.mul_succ_r*{.just} to n and 0, we have `n * 1 = n * 0 + n`{.claim}.
  - By application, we have `n * 0 + n = n`{.claim}.
    - By application, we have `Basics.flip Basics.impl (n * 0 + n = n) (0 + n = n)`, that is `0 + n = n -> n * 0 + n = n`{.claim}.
      - We have proved `n * 0 = 0 -> Basics.flip Basics.impl (n * 0 + n = n) (0 + n = n)`{.claim}.
        - Assume `n * 0 = 0`{.hyp} (lemma).
          - By application, we have `Morphisms.respectful eq (Basics.flip Basics.impl) (eq (n * 0 + n)) (eq (0 + n))`, that is `forall x y : nat, x = y -> Basics.flip Basics.impl (n * 0 + n = x) (0 + n = y)`{.claim}.
            - Applying *Morphisms.trans_co_eq_inv_impl_morphism*{.just} to nat, we have `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq (Basics.flip Basics.impl))) (@eq nat)`, that is `forall x y : nat, x = y -> Morphisms.respectful eq (Basics.flip Basics.impl) (eq x) (eq y)`{.claim}.
              - The element `eq` belongs to `Relation_Definitions.relation nat`.
              - Applying *RelationClasses.Equivalence_Transitive*{.just} to nat and *PeanoNat.Nat.eq_equiv*{.just}, we have `RelationClasses.Transitive (@eq nat)`{.claim}.
                - The element `eq` belongs to `Relation_Definitions.relation nat`.
            - The element `n * 0 + n` belongs to `nat`.
            - The element `0 + n` belongs to `nat`.
            - By application, with n and n, we have `n * 0 + n = 0 + n`{.claim}.
              - By application, with 0 and *lemma*{.just}, we have `Morphisms.respectful eq eq (Init.Nat.add (n * 0)) (Init.Nat.add 0)`, that is `forall x y : nat, x = y -> n * 0 + x = 0 + y`{.claim}.
                - By *PeanoNat.Nat.add_wd*{.just} we have `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Init.Nat.add`, that is `forall x y : nat, x = y -> Morphisms.respectful eq eq (Init.Nat.add x) (Init.Nat.add y)`{.claim}.
                - The element `n * 0` belongs to `nat`.
              - Applying *Morphisms.reflexive_proper_proxy*{.just} to nat and n, we have `Morphisms.ProperProxy eq n`, that is `n = n`{.claim}.
                - The element `eq` belongs to `Relation_Definitions.relation nat`.
                - Applying *Morphisms.reflexive_reflexive_proxy*{.just} to nat, we have `Morphisms.ReflexiveProxy (@eq nat)`{.claim}.
                  - The element `eq` belongs to `Relation_Definitions.relation nat`.
                  - Applying *RelationClasses.Equivalence_Reflexive*{.just} to nat and *PeanoNat.Nat.eq_equiv*{.just}, we have `RelationClasses.Reflexive (@eq nat)`{.claim}.
                    - The element `eq` belongs to `Relation_Definitions.relation nat`.
          - Applying *Morphisms.eq_proper_proxy*{.just} to nat and n, we have `Morphisms.ProperProxy eq n`, that is `n = n`{.claim}.

          By application, with n and n, we have `Basics.flip Basics.impl (n * 0 + n = n) (0 + n = n)`{.claim}.
      - Applying *PeanoNat.Nat.mul_0_r*{.just} to n, we have `n * 0 = 0`{.claim}.
    - By application, we have `0 + n = n`{.claim}.
      - By application, we have `Basics.flip Basics.impl (0 + n = n) (n = n)`, that is `n = n -> 0 + n = n`{.claim}.
        - We have proved `0 + n = n -> Basics.flip Basics.impl (0 + n = n) (n = n)`{.claim}.
          - Assume `0 + n = n`{.hyp} (lemma).
            - By application, with n and *lemma*{.just}, we have `Morphisms.respectful eq (Basics.flip Basics.impl) (eq (0 + n)) (eq n)`, that is `forall x y : nat, x = y -> Basics.flip Basics.impl (0 + n = x) (n = y)`{.claim}.
              - Applying *Morphisms.trans_co_eq_inv_impl_morphism*{.just} to nat, we have `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq (Basics.flip Basics.impl))) (@eq nat)`, that is `forall x y : nat, x = y -> Morphisms.respectful eq (Basics.flip Basics.impl) (eq x) (eq y)`{.claim}.
                - The element `eq` belongs to `Relation_Definitions.relation nat`.
                - Applying *RelationClasses.Equivalence_Transitive*{.just} to nat and *PeanoNat.Nat.eq_equiv*{.just}, we have `RelationClasses.Transitive (@eq nat)`{.claim}.
                  - The element `eq` belongs to `Relation_Definitions.relation nat`.
              - The element `0 + n` belongs to `nat`.
            - Applying *Morphisms.eq_proper_proxy*{.just} to nat and n, we have `Morphisms.ProperProxy eq n`, that is `n = n`{.claim}.

            By application, with n and n, we have `Basics.flip Basics.impl (0 + n = n) (n = n)`{.claim}.
        - Applying *PeanoNat.Nat.add_0_l*{.just} to n, we have `0 + n = n`{.claim}.
      - Applying *RelationClasses.reflexivity*{.just} to nat and n, we have `n = n`{.claim}.
        - The element `eq` belongs to `Relation_Definitions.relation nat`.
        - Applying *RelationClasses.Equivalence_Reflexive*{.just} to nat and *PeanoNat.Nat.eq_equiv*{.just}, we have `RelationClasses.Reflexive (@eq nat)`{.claim}.
          - The element `eq` belongs to `Relation_Definitions.relation nat`.
- By application, we have `n * 1 = n`{.claim}.
