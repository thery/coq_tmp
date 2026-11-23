---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# Nat.mul_comm

Let `n m : nat`{.var}. We prove `n * m = m * n`{.claim}.

- Thus we have `forall x y : nat, x = y -> x * m = m * x <-> y * m = m * y`{.claim}.
  - Let us choose arbitrarily `x : nat`{.var} and `y : nat`{.var}.
    - Assume `x = y`{.hyp} (H).
      - In particular `Morphisms.ProperProxy eq (y * m = m * y)`, that is `(y * m = m * y) = (y * m = m * y)`{.claim}.
        - Using *Morphisms.eq_proper_proxy*{.just} we get `forall (A : Type) (x0 : A), Morphisms.ProperProxy eq x0`{.claim}.
      - Using *RelationClasses.iff_Reflexive*{.just} we get `RelationClasses.Reflexive iff`{.claim}.
      - Using *RelationClasses.reflexivity*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x0 : A, R x0 x0`{.claim}.
      - We deduce `forall x0 : Prop, x0 <-> x0`{.claim}.
      - By *tauto*{.just} we deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (iff (x * m = m * x)) (iff (y * m = m * y))`, that is `forall x0 y0 : Prop, x0 = y0 -> Basics.flip Basics.impl (x * m = m * x <-> x0) (y * m = m * y <-> y0)`{.claim}.
        - By *H*{.just} we have `x = y`{.claim}.
        - We deduce `Morphisms.Proper (Morphisms.respectful eq eq) (Nat.mul m)`, that is `forall x0 y0 : nat, x0 = y0 -> m * x0 = m * y0`{.claim}.
          - In particular `Morphisms.ProperProxy eq m`{.claim}.
            - We deduce `Morphisms.ReflexiveProxy (@eq nat)`{.claim}.
              - We deduce `RelationClasses.Reflexive (@eq nat)`{.claim}.
                - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
                - Using *RelationClasses.Equivalence_Reflexive*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R`{.claim}.
              - Using *Morphisms.reflexive_reflexive_proxy*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> Morphisms.ReflexiveProxy R`{.claim}.
            - Using *Morphisms.reflexive_proper_proxy*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), Morphisms.ReflexiveProxy R -> forall x0 : A, Morphisms.ProperProxy R x0`{.claim}.
            - We deduce `forall x0 : nat, Morphisms.ProperProxy eq x0`{.claim}.
          - We deduce `forall x0 : nat, Morphisms.ProperProxy eq x0 -> Morphisms.Proper (Morphisms.respectful eq eq) (Nat.mul x0)`{.claim}.
            - Using *PeanoNat.Nat.mul_wd*{.just} we get `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Init.Nat.mul`{.claim}.
            - Using *Morphisms.Reflexive_partial_app_morphism*{.just} we get `forall (A B : Type) (R : Relation_Definitions.relation A) (R' : Relation_Definitions.relation B) (m0 : A -> B), Morphisms.Proper (Morphisms.respectful R R') m0 -> forall x0 : A, Morphisms.ProperProxy R x0 -> Morphisms.Proper R' (m0 x0)`{.claim}.
        - By *tauto*{.just} we deduce `Morphisms.respectful eq iff (eq (x * m)) (eq (y * m))`, that is `forall x0 y0 : nat, x0 = y0 -> x * m = x0 <-> y * m = y0`{.claim}.
          - In particular `Morphisms.ProperProxy eq m`, that is `m = m`{.claim}.
            - We deduce `Morphisms.ReflexiveProxy (@eq nat)`{.claim}.
              - We deduce `RelationClasses.Reflexive (@eq nat)`{.claim}.
                - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
                - Using *RelationClasses.Equivalence_Reflexive*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R`{.claim}.
              - Using *Morphisms.reflexive_reflexive_proxy*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> Morphisms.ReflexiveProxy R`{.claim}.
            - Using *Morphisms.reflexive_proper_proxy*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), Morphisms.ReflexiveProxy R -> forall x0 : A, Morphisms.ProperProxy R x0`{.claim}.
            - We deduce `forall x0 : nat, Morphisms.ProperProxy eq x0`{.claim}.
          - We deduce `Morphisms.respectful eq eq (Init.Nat.mul x) (Init.Nat.mul y)`, that is `forall x0 y0 : nat, x0 = y0 -> x * x0 = y * y0`{.claim}.
            - By *H*{.just} we have `x = y`{.claim}.
            - Using *PeanoNat.Nat.mul_wd*{.just} we get `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Init.Nat.mul`, that is `forall x0 y0 : nat, x0 = y0 -> Morphisms.respectful eq eq (Init.Nat.mul x0) (Init.Nat.mul y0)`{.claim}.
          - We deduce `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq iff)) (@eq nat)`, that is `forall x0 y0 : nat, x0 = y0 -> Morphisms.respectful eq iff (eq x0) (eq y0)`{.claim}.
            - We deduce `RelationClasses.PER (@eq nat)`{.claim}.
              - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
              - Using *RelationClasses.Equivalence_PER*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R`{.claim}.
            - Using *Morphisms.PER_morphism*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful R iff)) R`{.claim}.
        - We deduce `Morphisms.Proper (Morphisms.respectful iff (Morphisms.respectful eq (Basics.flip Basics.impl))) iff`, that is `forall x0 y0 : Prop, x0 <-> y0 -> Morphisms.respectful eq (Basics.flip Basics.impl) (iff x0) (iff y0)`{.claim}.
          - Using *RelationClasses.iff_Transitive*{.just} we get `RelationClasses.Transitive iff`{.claim}.
          - Using *Morphisms.trans_co_eq_inv_impl_morphism*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Transitive R -> Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful eq (Basics.flip Basics.impl))) R`{.claim}.

      By *lia*{.just} we deduce `x * m = m * x <-> y * m = m * y`{.claim}.

    We have proved `x = y -> x * m = m * x <-> y * m = m * y`{.claim}.
- Using *PeanoNat.Nat.mul_0_r*{.just} we get `forall n0 : nat, n0 * 0 = 0`{.claim}.
- Using *PeanoNat.Nat.mul_0_l*{.just} we get `forall n0 : nat, 0 * n0 = 0`{.claim}.
- In particular `0 = 0`, that is `0 = 0`{.claim}.
  - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
  - Using *RelationClasses.Equivalence_Reflexive*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R`{.claim}.
  - Using *RelationClasses.reflexivity*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x : A, R x x`{.claim}.
  - By *tauto*{.just} we deduce `forall x : nat, x = x`{.claim}.
- We have proved `0 * m = 0 -> Basics.flip Basics.impl (0 * m = 0) (0 = 0)`{.claim}.
  - Assume `0 * m = 0`{.hyp} (lemma).
    - In particular `Morphisms.ProperProxy eq 0`, that is `0 = 0`{.claim}.
      - Using *Morphisms.eq_proper_proxy*{.just} we get `forall (A : Type) (x : A), Morphisms.ProperProxy eq x`{.claim}.
    - We deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (eq (0 * m)) (eq 0)`, that is `forall x y : nat, x = y -> Basics.flip Basics.impl (0 * m = x) (0 = y)`{.claim}.
      - By *lemma*{.just} we have `0 * m = 0`{.claim}.
      - We deduce `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq (Basics.flip Basics.impl))) (@eq nat)`, that is `forall x y : nat, x = y -> Morphisms.respectful eq (Basics.flip Basics.impl) (eq x) (eq y)`{.claim}.
        - We deduce `RelationClasses.Transitive (@eq nat)`{.claim}.
          - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
          - Using *RelationClasses.Equivalence_Transitive*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Transitive R`{.claim}.
        - Using *Morphisms.trans_co_eq_inv_impl_morphism*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Transitive R -> Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful eq (Basics.flip Basics.impl))) R`{.claim}.

    We deduce `Basics.flip Basics.impl (0 * m = 0) (0 = 0)`{.claim}.
- We have proved `m * 0 = 0 -> Basics.flip Basics.impl (0 * m = m * 0) (0 * m = 0)`{.claim}.
  - Assume `m * 0 = 0`{.hyp} (lemma).
    - By *lemma*{.just} we have `m * 0 = 0`{.claim}.
    - We deduce `RelationClasses.PER (@eq nat)`{.claim}.
      - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
      - Using *RelationClasses.Equivalence_PER*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R`{.claim}.
    - Using *Morphisms.trans_sym_co_inv_impl_morphism*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> forall x : A, Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)`{.claim}.

    By *congruence*{.just} we deduce `Basics.flip Basics.impl (0 * m = m * 0) (0 * m = 0)`{.claim}.
- By *lia*{.just} we have `forall n0 : nat, n0 * m = m * n0 <-> S n0 * m = m * S n0`{.claim}.
- Using *PeanoNat.Nat.bi_induction*{.just} we get `forall A : nat -> Prop, Morphisms.Proper (Morphisms.respectful eq iff) A -> A 0 -> (forall n0 : nat, A n0 <-> A (S n0)) -> forall n0 : nat, A n0`{.claim}.
- By *lia*{.just} we deduce `forall n0 : nat, n0 * m = m * n0`{.claim}.
- In particular `n * m = m * n`{.claim}.
