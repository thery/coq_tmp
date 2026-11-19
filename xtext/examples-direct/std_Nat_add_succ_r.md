---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# Nat.add_succ_r

Let `n m : nat`{.var}. We prove `n + S m = S (n + m)`{.claim}.

- Thus we have `forall x y : nat, x = y -> x + S m = S (x + m) <-> y + S m = S (y + m)`{.claim}.
  - Let us choose arbitrarily `x : nat`{.var} and `y : nat`{.var}.
    - Assume `x = y`{.hyp} (H).
      - In particular `Morphisms.ProperProxy eq (y + S m = S (y + m))`, that is `(y + S m = S (y + m)) = (y + S m = S (y + m))`{.claim}.
        - Using *Morphisms.eq_proper_proxy*{.just} we get `forall (A : Type) (x0 : A), Morphisms.ProperProxy eq x0`{.claim}.
      - Using *RelationClasses.iff_Reflexive*{.just} we get `RelationClasses.Reflexive iff`{.claim}.
      - Using *RelationClasses.reflexivity*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x0 : A, R x0 x0`{.claim}.
      - We deduce `forall x0 : Prop, x0 <-> x0`{.claim}.
      - By *congruence*{.just} we deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (iff (x + S m = S (x + m))) (iff (y + S m = S (y + m)))`, that is `forall x0 y0 : Prop, x0 = y0 -> Basics.flip Basics.impl (x + S m = S (x + m) <-> x0) (y + S m = S (y + m) <-> y0)`{.claim}.
        - In particular `Morphisms.ProperProxy eq m`, that is `m = m`{.claim}.
          - We deduce `Morphisms.ReflexiveProxy (@eq nat)`{.claim}.
            - We deduce `RelationClasses.Reflexive (@eq nat)`{.claim}.
              - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
              - Using *RelationClasses.Equivalence_Reflexive*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R`{.claim}.
            - Using *Morphisms.reflexive_reflexive_proxy*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> Morphisms.ReflexiveProxy R`{.claim}.
          - Using *Morphisms.reflexive_proper_proxy*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), Morphisms.ReflexiveProxy R -> forall x0 : A, Morphisms.ProperProxy R x0`{.claim}.
          - We deduce `forall x0 : nat, Morphisms.ProperProxy eq x0`{.claim}.
        - We deduce `Morphisms.respectful eq eq (Init.Nat.add x) (Init.Nat.add y)`, that is `forall x0 y0 : nat, x0 = y0 -> x + x0 = y + y0`{.claim}.
          - By *H*{.just} we have `x = y`{.claim}.
          - Using *PeanoNat.Nat.add_wd*{.just} we get `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Init.Nat.add`, that is `forall x0 y0 : nat, x0 = y0 -> Morphisms.respectful eq eq (Init.Nat.add x0) (Init.Nat.add y0)`{.claim}.
        - Using *PeanoNat.Nat.succ_wd*{.just} we get `Morphisms.Proper (Morphisms.respectful eq eq) S`, that is `forall x0 y0 : nat, x0 = y0 -> S x0 = S y0`{.claim}.
        - By *firstorder*{.just} we deduce `Morphisms.respectful eq iff (eq (x + S m)) (eq (y + S m))`, that is `forall x0 y0 : nat, x0 = y0 -> x + S m = x0 <-> y + S m = y0`{.claim}.
          - In particular `Morphisms.ProperProxy eq (S m)`, that is `S m = S m`{.claim}.
            - We deduce `Morphisms.ReflexiveProxy (@eq nat)`{.claim}.
              - We deduce `RelationClasses.Reflexive (@eq nat)`{.claim}.
                - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
                - Using *RelationClasses.Equivalence_Reflexive*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R`{.claim}.
              - Using *Morphisms.reflexive_reflexive_proxy*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> Morphisms.ReflexiveProxy R`{.claim}.
            - Using *Morphisms.reflexive_proper_proxy*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), Morphisms.ReflexiveProxy R -> forall x0 : A, Morphisms.ProperProxy R x0`{.claim}.
            - We deduce `forall x0 : nat, Morphisms.ProperProxy eq x0`{.claim}.
          - We deduce `Morphisms.respectful eq eq (Init.Nat.add x) (Init.Nat.add y)`, that is `forall x0 y0 : nat, x0 = y0 -> x + x0 = y + y0`{.claim}.
            - By *H*{.just} we have `x = y`{.claim}.
            - Using *PeanoNat.Nat.add_wd*{.just} we get `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Init.Nat.add`, that is `forall x0 y0 : nat, x0 = y0 -> Morphisms.respectful eq eq (Init.Nat.add x0) (Init.Nat.add y0)`{.claim}.
          - We deduce `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq iff)) (@eq nat)`, that is `forall x0 y0 : nat, x0 = y0 -> Morphisms.respectful eq iff (eq x0) (eq y0)`{.claim}.
            - We deduce `RelationClasses.PER (@eq nat)`{.claim}.
              - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
              - Using *RelationClasses.Equivalence_PER*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R`{.claim}.
            - Using *Morphisms.PER_morphism*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful R iff)) R`{.claim}.
        - We deduce `Morphisms.Proper (Morphisms.respectful iff (Morphisms.respectful eq (Basics.flip Basics.impl))) iff`, that is `forall x0 y0 : Prop, x0 <-> y0 -> Morphisms.respectful eq (Basics.flip Basics.impl) (iff x0) (iff y0)`{.claim}.
          - Using *RelationClasses.iff_Transitive*{.just} we get `RelationClasses.Transitive iff`{.claim}.
          - Using *Morphisms.trans_co_eq_inv_impl_morphism*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Transitive R -> Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful eq (Basics.flip Basics.impl))) R`{.claim}.

      By *lia*{.just} we deduce `x + S m = S (x + m) <-> y + S m = S (y + m)`{.claim}.

    We have proved `x = y -> x + S m = S (x + m) <-> y + S m = S (y + m)`{.claim}.
- Using *PeanoNat.Nat.add_0_l*{.just} we get `forall n0 : nat, 0 + n0 = n0`{.claim}.
- Using *PeanoNat.Nat.add_0_l*{.just} we get `forall n0 : nat, 0 + n0 = n0`{.claim}.
- In particular `S m = S m`, that is `S m = S m`{.claim}.
  - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
  - Using *RelationClasses.Equivalence_Reflexive*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R`{.claim}.
  - Using *RelationClasses.reflexivity*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x : A, R x x`{.claim}.
  - By *tauto*{.just} we deduce `forall x : nat, x = x`{.claim}.
- We have proved `0 + m = m -> Basics.flip Basics.impl (S m = S (0 + m)) (S m = S m)`{.claim}.
  - Assume `0 + m = m`{.hyp} (lemma).
    - By *lemma*{.just} we have `0 + m = m`{.claim}.
    - Using *PeanoNat.Nat.succ_wd*{.just} we get `Morphisms.Proper (Morphisms.respectful eq eq) S`, that is `forall x y : nat, x = y -> S x = S y`{.claim}.
    - We deduce `RelationClasses.PER (@eq nat)`{.claim}.
      - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
      - Using *RelationClasses.Equivalence_PER*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R`{.claim}.
    - Using *Morphisms.trans_sym_co_inv_impl_morphism*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> forall x : A, Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)`{.claim}.

    By *congruence*{.just} we deduce `Basics.flip Basics.impl (S m = S (0 + m)) (S m = S m)`{.claim}.
- We have proved `0 + S m = S m -> Basics.flip Basics.impl (0 + S m = S (0 + m)) (S m = S (0 + m))`{.claim}.
  - Assume `0 + S m = S m`{.hyp} (lemma).
    - In particular `Morphisms.ProperProxy eq (S (0 + m))`, that is `S (0 + m) = S (0 + m)`{.claim}.
      - Using *Morphisms.eq_proper_proxy*{.just} we get `forall (A : Type) (x : A), Morphisms.ProperProxy eq x`{.claim}.
    - We deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (eq (0 + S m)) (eq (S m))`, that is `forall x y : nat, x = y -> Basics.flip Basics.impl (0 + S m = x) (S m = y)`{.claim}.
      - By *lemma*{.just} we have `0 + S m = S m`{.claim}.
      - We deduce `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq (Basics.flip Basics.impl))) (@eq nat)`, that is `forall x y : nat, x = y -> Morphisms.respectful eq (Basics.flip Basics.impl) (eq x) (eq y)`{.claim}.
        - We deduce `RelationClasses.Transitive (@eq nat)`{.claim}.
          - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
          - Using *RelationClasses.Equivalence_Transitive*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Transitive R`{.claim}.
        - Using *Morphisms.trans_co_eq_inv_impl_morphism*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Transitive R -> Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful eq (Basics.flip Basics.impl))) R`{.claim}.

    We deduce `Basics.flip Basics.impl (0 + S m = S (0 + m)) (S m = S (0 + m))`{.claim}.
- By *lia*{.just} we have `forall n0 : nat, n0 + S m = S (n0 + m) <-> S n0 + S m = S (S n0 + m)`{.claim}.
- Using *PeanoNat.Nat.bi_induction*{.just} we get `forall A : nat -> Prop, Morphisms.Proper (Morphisms.respectful eq iff) A -> A 0 -> (forall n0 : nat, A n0 <-> A (S n0)) -> forall n0 : nat, A n0`{.claim}.
- By *lia*{.just} we deduce `forall n0 : nat, n0 + S m = S (n0 + m)`{.claim}.
- In particular `n + S m = S (n + m)`{.claim}.
