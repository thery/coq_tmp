---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# Nat.mul_1_r

Let `n : nat`{.var}. We prove `n * 1 = n`{.claim}.

- We have proved `1 = 1 -> Basics.flip Basics.impl (n * 1 = n) (n * 1 = n)`{.claim} (P1).
  - Assume `1 = 1`{.hyp} (lemma).
    - Applying *RelationClasses.Equivalence_Transitive*{.just} to nat and *PeanoNat.Nat.eq_equiv*{.just}, we have `RelationClasses.Transitive (@eq nat)`{.claim} (P1.1).
      - The element `eq` belongs to `Relation_Definitions.relation nat`.
    - Applying *Morphisms.trans_co_eq_inv_impl_morphism*{.just} to nat and P1.1, we have `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq (Basics.flip Basics.impl))) (@eq nat)`, that is `forall x y : nat, x = y -> Morphisms.respectful eq (Basics.flip Basics.impl) (eq x) (eq y)`{.claim} (P1.2).
      - The element `eq` belongs to `Relation_Definitions.relation nat`.
    - Applying *RelationClasses.Equivalence_Reflexive*{.just} to nat and *PeanoNat.Nat.eq_equiv*{.just}, we have `RelationClasses.Reflexive (@eq nat)`{.claim} (P1.3).
      - The element `eq` belongs to `Relation_Definitions.relation nat`.
    - Applying *Morphisms.reflexive_reflexive_proxy*{.just} to nat and P1.3, we have `Morphisms.ReflexiveProxy (@eq nat)`{.claim} (P1.4).
      - The element `eq` belongs to `Relation_Definitions.relation nat`.
    - Applying *Morphisms.reflexive_proper_proxy*{.just} to nat, P1.4 and n, we have `Morphisms.ProperProxy eq n`{.claim} (P1.5).
      - The element `eq` belongs to `Relation_Definitions.relation nat`.
    - Applying *Morphisms.Reflexive_partial_app_morphism*{.just} to nat, Nat.mul, *PeanoNat.Nat.mul_wd*{.just}, n and P1.5, we have `Morphisms.Proper (Morphisms.respectful eq eq) (Nat.mul n)`, that is `forall x y : nat, x = y -> n * x = n * y`{.claim} (P1.6).
      - The element `nat -> nat` belongs to `Type`.
      - The element `eq` belongs to `Relation_Definitions.relation nat`.
      - The element `Morphisms.respectful eq eq` belongs to `Relation_Definitions.relation (nat -> nat)`.
    - Applying P1.6 to *lemma*{.just}, we have `n * 1 = n * 1`{.claim} (P1.7).
      - The element `1` belongs to `nat`.
      - The element `1` belongs to `nat`.
    - Applying P1.2 to P1.7, we have `Morphisms.respectful eq (Basics.flip Basics.impl) (eq (n * 1)) (eq (n * 1))`, that is `forall x y : nat, x = y -> Basics.flip Basics.impl (n * 1 = x) (n * 1 = y)`{.claim} (P1.8).
      - The element `n * 1` belongs to `nat`.
      - The element `n * 1` belongs to `nat`.
    - Applying *Morphisms.eq_proper_proxy*{.just} to nat and n, we have `Morphisms.ProperProxy eq n`, that is `n = n`{.claim} (P1.9).

    Applying P1.8 to n, n and P1.9, we have `Basics.flip Basics.impl (n * 1 = n) (n * 1 = n)`{.claim}.
- Applying *P1*{.just} to *PeanoNat.Nat.one_succ*{.just}, we have `Basics.flip Basics.impl (n * 1 = n) (n * 1 = n)`, that is `n * 1 = n -> n * 1 = n`{.claim} (P2).
- We have proved `n * 1 = n * 0 + n -> Basics.flip Basics.impl (n * 1 = n) (n * 0 + n = n)`{.claim} (P3).
  - Assume `n * 1 = n * 0 + n`{.hyp} (lemma).
    - Applying *RelationClasses.Equivalence_Transitive*{.just} to nat and *PeanoNat.Nat.eq_equiv*{.just}, we have `RelationClasses.Transitive (@eq nat)`{.claim} (P3.1).
      - The element `eq` belongs to `Relation_Definitions.relation nat`.
    - Applying *Morphisms.trans_co_eq_inv_impl_morphism*{.just} to nat and P3.1, we have `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq (Basics.flip Basics.impl))) (@eq nat)`, that is `forall x y : nat, x = y -> Morphisms.respectful eq (Basics.flip Basics.impl) (eq x) (eq y)`{.claim} (P3.2).
      - The element `eq` belongs to `Relation_Definitions.relation nat`.
    - Applying P3.2 to *lemma*{.just}, we have `Morphisms.respectful eq (Basics.flip Basics.impl) (eq (n * 1)) (eq (n * 0 + n))`, that is `forall x y : nat, x = y -> Basics.flip Basics.impl (n * 1 = x) (n * 0 + n = y)`{.claim} (P3.3).
      - The element `n * 1` belongs to `nat`.
      - The element `n * 0 + n` belongs to `nat`.
    - Applying *Morphisms.eq_proper_proxy*{.just} to nat and n, we have `Morphisms.ProperProxy eq n`, that is `n = n`{.claim} (P3.4).

    Applying P3.3 to n, n and P3.4, we have `Basics.flip Basics.impl (n * 1 = n) (n * 0 + n = n)`{.claim}.
- Applying *PeanoNat.Nat.mul_succ_r*{.just} to n and 0, we have `n * 1 = n * 0 + n`{.claim} (P4).
- Applying *P3*{.just} to *P4*{.just}, we have `Basics.flip Basics.impl (n * 1 = n) (n * 0 + n = n)`, that is `n * 0 + n = n -> n * 1 = n`{.claim} (P5).
- We have proved `n * 0 = 0 -> Basics.flip Basics.impl (n * 0 + n = n) (0 + n = n)`{.claim} (P6).
  - Assume `n * 0 = 0`{.hyp} (lemma).
    - Applying *RelationClasses.Equivalence_Transitive*{.just} to nat and *PeanoNat.Nat.eq_equiv*{.just}, we have `RelationClasses.Transitive (@eq nat)`{.claim} (P6.1).
      - The element `eq` belongs to `Relation_Definitions.relation nat`.
    - Applying *Morphisms.trans_co_eq_inv_impl_morphism*{.just} to nat and P6.1, we have `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq (Basics.flip Basics.impl))) (@eq nat)`, that is `forall x y : nat, x = y -> Morphisms.respectful eq (Basics.flip Basics.impl) (eq x) (eq y)`{.claim} (P6.2).
      - The element `eq` belongs to `Relation_Definitions.relation nat`.
    - By *PeanoNat.Nat.add_wd*{.just} we have `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Init.Nat.add`, that is `forall x y : nat, x = y -> Morphisms.respectful eq eq (Init.Nat.add x) (Init.Nat.add y)`{.claim} (P6.3).
    - Applying P6.3 to 0 and *lemma*{.just}, we have `Morphisms.respectful eq eq (Init.Nat.add (n * 0)) (Init.Nat.add 0)`, that is `forall x y : nat, x = y -> n * 0 + x = 0 + y`{.claim} (P6.4).
      - The element `n * 0` belongs to `nat`.
    - Applying *RelationClasses.Equivalence_Reflexive*{.just} to nat and *PeanoNat.Nat.eq_equiv*{.just}, we have `RelationClasses.Reflexive (@eq nat)`{.claim} (P6.5).
      - The element `eq` belongs to `Relation_Definitions.relation nat`.
    - Applying *Morphisms.reflexive_reflexive_proxy*{.just} to nat and P6.5, we have `Morphisms.ReflexiveProxy (@eq nat)`{.claim} (P6.6).
      - The element `eq` belongs to `Relation_Definitions.relation nat`.
    - Applying *Morphisms.reflexive_proper_proxy*{.just} to nat, P6.6 and n, we have `Morphisms.ProperProxy eq n`, that is `n = n`{.claim} (P6.7).
      - The element `eq` belongs to `Relation_Definitions.relation nat`.
    - Applying P6.4 to n, n and P6.7, we have `n * 0 + n = 0 + n`{.claim} (P6.8).
    - Applying P6.2 to P6.8, we have `Morphisms.respectful eq (Basics.flip Basics.impl) (eq (n * 0 + n)) (eq (0 + n))`, that is `forall x y : nat, x = y -> Basics.flip Basics.impl (n * 0 + n = x) (0 + n = y)`{.claim} (P6.9).
      - The element `n * 0 + n` belongs to `nat`.
      - The element `0 + n` belongs to `nat`.
    - Applying *Morphisms.eq_proper_proxy*{.just} to nat and n, we have `Morphisms.ProperProxy eq n`, that is `n = n`{.claim} (P6.10).

    Applying P6.9 to n, n and P6.10, we have `Basics.flip Basics.impl (n * 0 + n = n) (0 + n = n)`{.claim}.
- Applying *PeanoNat.Nat.mul_0_r*{.just} to n, we have `n * 0 = 0`{.claim} (P7).
- Applying *P6*{.just} to *P7*{.just}, we have `Basics.flip Basics.impl (n * 0 + n = n) (0 + n = n)`, that is `0 + n = n -> n * 0 + n = n`{.claim} (P8).
- We have proved `0 + n = n -> Basics.flip Basics.impl (0 + n = n) (n = n)`{.claim} (P9).
  - Assume `0 + n = n`{.hyp} (lemma).
    - Applying *RelationClasses.Equivalence_Transitive*{.just} to nat and *PeanoNat.Nat.eq_equiv*{.just}, we have `RelationClasses.Transitive (@eq nat)`{.claim} (P9.1).
      - The element `eq` belongs to `Relation_Definitions.relation nat`.
    - Applying *Morphisms.trans_co_eq_inv_impl_morphism*{.just} to nat and P9.1, we have `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq (Basics.flip Basics.impl))) (@eq nat)`, that is `forall x y : nat, x = y -> Morphisms.respectful eq (Basics.flip Basics.impl) (eq x) (eq y)`{.claim} (P9.2).
      - The element `eq` belongs to `Relation_Definitions.relation nat`.
    - Applying P9.2 to n and *lemma*{.just}, we have `Morphisms.respectful eq (Basics.flip Basics.impl) (eq (0 + n)) (eq n)`, that is `forall x y : nat, x = y -> Basics.flip Basics.impl (0 + n = x) (n = y)`{.claim} (P9.3).
      - The element `0 + n` belongs to `nat`.
    - Applying *Morphisms.eq_proper_proxy*{.just} to nat and n, we have `Morphisms.ProperProxy eq n`, that is `n = n`{.claim} (P9.4).

    Applying P9.3 to n, n and P9.4, we have `Basics.flip Basics.impl (0 + n = n) (n = n)`{.claim}.
- Applying *PeanoNat.Nat.add_0_l*{.just} to n, we have `0 + n = n`{.claim} (P10).
- Applying *P9*{.just} to *P10*{.just}, we have `Basics.flip Basics.impl (0 + n = n) (n = n)`, that is `n = n -> 0 + n = n`{.claim} (P11).
- Applying *RelationClasses.Equivalence_Reflexive*{.just} to nat and *PeanoNat.Nat.eq_equiv*{.just}, we have `RelationClasses.Reflexive (@eq nat)`{.claim} (P12).
  - The element `eq` belongs to `Relation_Definitions.relation nat`.
- Applying *RelationClasses.reflexivity*{.just} to nat, *P12*{.just} and n, we have `n = n`{.claim} (P13).
  - The element `eq` belongs to `Relation_Definitions.relation nat`.
- Applying *P11*{.just} to *P13*{.just}, we have `0 + n = n`{.claim} (P14).
- Applying *P8*{.just} to *P14*{.just}, we have `n * 0 + n = n`{.claim} (P15).
- Applying *P5*{.just} to *P15*{.just}, we have `n * 1 = n`{.claim} (P16).
- Applying *P2*{.just} to *P16*{.just}, we have `n * 1 = n`{.claim}.
