---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# Nat.mul_1_r

Let `n : nat`{.var}. We prove `n * 1 = n`{.claim}.

- Using *PeanoNat.Nat.one_succ*{.just} we get `1 = 1`{.claim}.
- Using *PeanoNat.Nat.mul_succ_r*{.just} we get `forall n0 m : nat, n0 * S m = n0 * m + n0`{.claim}.
- Using *PeanoNat.Nat.mul_0_r*{.just} we get `forall n0 : nat, n0 * 0 = 0`{.claim}.
- Using *PeanoNat.Nat.add_0_l*{.just} we get `forall n0 : nat, 0 + n0 = n0`{.claim}.
- In particular `n = n`, that is `n = n`{.claim}.
  - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
  - Using *RelationClasses.Equivalence_Reflexive*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R`{.claim}.
  - Using *RelationClasses.reflexivity*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x : A, R x x`{.claim}.
  - By *tauto*{.just} we deduce `forall x : nat, x = x`{.claim}.
- We have proved `0 + n = n -> Basics.flip Basics.impl (0 + n = n) (n = n)`{.claim}.
  - Assume `0 + n = n`{.hyp} (lemma).
    - In particular `Morphisms.ProperProxy eq n`, that is `n = n`{.claim}.
      - Using *Morphisms.eq_proper_proxy*{.just} we get `forall (A : Type) (x : A), Morphisms.ProperProxy eq x`{.claim}.
    - We deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (eq (0 + n)) (eq n)`, that is `forall x y : nat, x = y -> Basics.flip Basics.impl (0 + n = x) (n = y)`{.claim}.
      - By *lemma*{.just} we have `0 + n = n`{.claim}.
      - We deduce `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq (Basics.flip Basics.impl))) (@eq nat)`, that is `forall x y : nat, x = y -> Morphisms.respectful eq (Basics.flip Basics.impl) (eq x) (eq y)`{.claim}.
        - We deduce `RelationClasses.Transitive (@eq nat)`{.claim}.
          - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
          - Using *RelationClasses.Equivalence_Transitive*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Transitive R`{.claim}.
        - Using *Morphisms.trans_co_eq_inv_impl_morphism*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Transitive R -> Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful eq (Basics.flip Basics.impl))) R`{.claim}.

    We deduce `Basics.flip Basics.impl (0 + n = n) (n = n)`{.claim}.
- We have proved `n * 0 = 0 -> Basics.flip Basics.impl (n * 0 + n = n) (0 + n = n)`{.claim}.
  - Assume `n * 0 = 0`{.hyp} (lemma).
    - In particular `Morphisms.ProperProxy eq n`, that is `n = n`{.claim}.
      - Using *Morphisms.eq_proper_proxy*{.just} we get `forall (A : Type) (x : A), Morphisms.ProperProxy eq x`{.claim}.
    - By *congruence*{.just} we deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (eq (n * 0 + n)) (eq (0 + n))`, that is `forall x y : nat, x = y -> Basics.flip Basics.impl (n * 0 + n = x) (0 + n = y)`{.claim}.
      - In particular `Morphisms.ProperProxy eq n`, that is `n = n`{.claim}.
        - We deduce `Morphisms.ReflexiveProxy (@eq nat)`{.claim}.
          - We deduce `RelationClasses.Reflexive (@eq nat)`{.claim}.
            - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
            - Using *RelationClasses.Equivalence_Reflexive*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R`{.claim}.
          - Using *Morphisms.reflexive_reflexive_proxy*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> Morphisms.ReflexiveProxy R`{.claim}.
        - Using *Morphisms.reflexive_proper_proxy*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), Morphisms.ReflexiveProxy R -> forall x : A, Morphisms.ProperProxy R x`{.claim}.
        - We deduce `forall x : nat, Morphisms.ProperProxy eq x`{.claim}.
      - We deduce `Morphisms.respectful eq eq (Init.Nat.add (n * 0)) (Init.Nat.add 0)`, that is `forall x y : nat, x = y -> n * 0 + x = 0 + y`{.claim}.
        - By *lemma*{.just} we have `n * 0 = 0`{.claim}.
        - Using *PeanoNat.Nat.add_wd*{.just} we get `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Init.Nat.add`, that is `forall x y : nat, x = y -> Morphisms.respectful eq eq (Init.Nat.add x) (Init.Nat.add y)`{.claim}.
      - We deduce `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq (Basics.flip Basics.impl))) (@eq nat)`, that is `forall x y : nat, x = y -> Morphisms.respectful eq (Basics.flip Basics.impl) (eq x) (eq y)`{.claim}.
        - We deduce `RelationClasses.Transitive (@eq nat)`{.claim}.
          - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
          - Using *RelationClasses.Equivalence_Transitive*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Transitive R`{.claim}.
        - Using *Morphisms.trans_co_eq_inv_impl_morphism*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Transitive R -> Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful eq (Basics.flip Basics.impl))) R`{.claim}.

    We deduce `Basics.flip Basics.impl (n * 0 + n = n) (0 + n = n)`{.claim}.
- We have proved `n * 1 = n * 0 + n -> Basics.flip Basics.impl (n * 1 = n) (n * 0 + n = n)`{.claim}.
  - Assume `n * 1 = n * 0 + n`{.hyp} (lemma).
    - In particular `Morphisms.ProperProxy eq n`, that is `n = n`{.claim}.
      - Using *Morphisms.eq_proper_proxy*{.just} we get `forall (A : Type) (x : A), Morphisms.ProperProxy eq x`{.claim}.
    - We deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (eq (n * 1)) (eq (n * 0 + n))`, that is `forall x y : nat, x = y -> Basics.flip Basics.impl (n * 1 = x) (n * 0 + n = y)`{.claim}.
      - By *lemma*{.just} we have `n * 1 = n * 0 + n`{.claim}.
      - We deduce `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq (Basics.flip Basics.impl))) (@eq nat)`, that is `forall x y : nat, x = y -> Morphisms.respectful eq (Basics.flip Basics.impl) (eq x) (eq y)`{.claim}.
        - We deduce `RelationClasses.Transitive (@eq nat)`{.claim}.
          - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
          - Using *RelationClasses.Equivalence_Transitive*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Transitive R`{.claim}.
        - Using *Morphisms.trans_co_eq_inv_impl_morphism*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Transitive R -> Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful eq (Basics.flip Basics.impl))) R`{.claim}.

    We deduce `Basics.flip Basics.impl (n * 1 = n) (n * 0 + n = n)`{.claim}.
- We have proved `1 = 1 -> Basics.flip Basics.impl (n * 1 = n) (n * 1 = n)`{.claim}.
  - Assume `1 = 1`{.hyp} (lemma).
    - In particular `Morphisms.ProperProxy eq n`, that is `n = n`{.claim}.
      - Using *Morphisms.eq_proper_proxy*{.just} we get `forall (A : Type) (x : A), Morphisms.ProperProxy eq x`{.claim}.
    - By *congruence*{.just} we deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (eq (n * 1)) (eq (n * 1))`, that is `forall x y : nat, x = y -> Basics.flip Basics.impl (n * 1 = x) (n * 1 = y)`{.claim}.
      - By *lemma*{.just} we have `1 = 1`{.claim}.
      - We deduce `Morphisms.Proper (Morphisms.respectful eq eq) (Nat.mul n)`, that is `forall x y : nat, x = y -> n * x = n * y`{.claim}.
        - In particular `Morphisms.ProperProxy eq n`{.claim}.
          - We deduce `Morphisms.ReflexiveProxy (@eq nat)`{.claim}.
            - We deduce `RelationClasses.Reflexive (@eq nat)`{.claim}.
              - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
              - Using *RelationClasses.Equivalence_Reflexive*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R`{.claim}.
            - Using *Morphisms.reflexive_reflexive_proxy*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> Morphisms.ReflexiveProxy R`{.claim}.
          - Using *Morphisms.reflexive_proper_proxy*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), Morphisms.ReflexiveProxy R -> forall x : A, Morphisms.ProperProxy R x`{.claim}.
          - We deduce `forall x : nat, Morphisms.ProperProxy eq x`{.claim}.
        - We deduce `forall x : nat, Morphisms.ProperProxy eq x -> Morphisms.Proper (Morphisms.respectful eq eq) (Nat.mul x)`{.claim}.
          - Using *PeanoNat.Nat.mul_wd*{.just} we get `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Init.Nat.mul`{.claim}.
          - Using *Morphisms.Reflexive_partial_app_morphism*{.just} we get `forall (A B : Type) (R : Relation_Definitions.relation A) (R' : Relation_Definitions.relation B) (m : A -> B), Morphisms.Proper (Morphisms.respectful R R') m -> forall x : A, Morphisms.ProperProxy R x -> Morphisms.Proper R' (m x)`{.claim}.
      - We deduce `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq (Basics.flip Basics.impl))) (@eq nat)`, that is `forall x y : nat, x = y -> Morphisms.respectful eq (Basics.flip Basics.impl) (eq x) (eq y)`{.claim}.
        - We deduce `RelationClasses.Transitive (@eq nat)`{.claim}.
          - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
          - Using *RelationClasses.Equivalence_Transitive*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Transitive R`{.claim}.
        - Using *Morphisms.trans_co_eq_inv_impl_morphism*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Transitive R -> Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful eq (Basics.flip Basics.impl))) R`{.claim}.

    We deduce `Basics.flip Basics.impl (n * 1 = n) (n * 1 = n)`{.claim}.
- By *congruence*{.just} we deduce `n * 1 = n`{.claim}.
