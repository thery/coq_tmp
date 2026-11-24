---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# Nat.add_0_r

Let `n : nat`{.var}. We prove `n + 0 = n`{.claim}.

- Thus we have `forall x y : nat, x = y -> x + 0 = x <-> y + 0 = y`{.claim}.
  - Let us choose arbitrarily `x : nat`{.var} and `y : nat`{.var}.
    - Assume `x = y`{.hyp} (H).
      - In particular `Morphisms.ProperProxy eq (y + 0 = y)`, that is `(y + 0 = y) = (y + 0 = y)`{.claim}.
        - Using *Morphisms.eq_proper_proxy*{.just} we get `forall (A : Type) (x0 : A), Morphisms.ProperProxy eq x0`{.claim}.
      - Using *RelationClasses.iff_Reflexive*{.just} we get `RelationClasses.Reflexive iff`{.claim}.
      - Using *RelationClasses.reflexivity*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x0 : A, R x0 x0`{.claim}.
      - We deduce `forall x0 : Prop, x0 <-> x0`{.claim}.
      - By *tauto*{.just} we deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (iff (x + 0 = x)) (iff (y + 0 = y))`, that is `forall x0 y0 : Prop, x0 = y0 -> Basics.flip Basics.impl (x + 0 = x <-> x0) (y + 0 = y <-> y0)`{.claim}.
        - By *H*{.just} we have `x = y`{.claim}.
        - By *tauto*{.just} we deduce `Morphisms.respectful eq iff (eq (x + 0)) (eq (y + 0))`, that is `forall x0 y0 : nat, x0 = y0 -> x + 0 = x0 <-> y + 0 = y0`{.claim}.
          - In particular `Morphisms.ProperProxy eq 0`, that is `0 = 0`{.claim}.
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

      By *tauto*{.just} we deduce `x + 0 = x <-> y + 0 = y`{.claim}.

    We have proved `x = y -> x + 0 = x <-> y + 0 = y`{.claim}.
- Using *PeanoNat.Nat.add_0_l*{.just} we get `forall n0 : nat, 0 + n0 = n0`{.claim}.
- In particular `0 = 0`, that is `0 = 0`{.claim}.
  - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
  - Using *RelationClasses.Equivalence_Reflexive*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R`{.claim}.
  - Using *RelationClasses.reflexivity*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x : A, R x x`{.claim}.
  - By *tauto*{.just} we deduce `forall x : nat, x = x`{.claim}.
- We have proved `0 + 0 = 0 -> Basics.flip Basics.impl (0 + 0 = 0) (0 = 0)`{.claim}.
  - Assume `0 + 0 = 0`{.hyp} (lemma).
    - In particular `Morphisms.ProperProxy eq 0`, that is `0 = 0`{.claim}.
      - Using *Morphisms.eq_proper_proxy*{.just} we get `forall (A : Type) (x : A), Morphisms.ProperProxy eq x`{.claim}.
    - We deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (eq (0 + 0)) (eq 0)`, that is `forall x y : nat, x = y -> Basics.flip Basics.impl (0 + 0 = x) (0 = y)`{.claim}.
      - By *lemma*{.just} we have `0 + 0 = 0`{.claim}.
      - We deduce `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq (Basics.flip Basics.impl))) (@eq nat)`, that is `forall x y : nat, x = y -> Morphisms.respectful eq (Basics.flip Basics.impl) (eq x) (eq y)`{.claim}.
        - We deduce `RelationClasses.Transitive (@eq nat)`{.claim}.
          - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
          - Using *RelationClasses.Equivalence_Transitive*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Transitive R`{.claim}.
        - Using *Morphisms.trans_co_eq_inv_impl_morphism*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Transitive R -> Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful eq (Basics.flip Basics.impl))) R`{.claim}.

    We deduce `Basics.flip Basics.impl (0 + 0 = 0) (0 = 0)`{.claim}.
- We have `forall n0 : nat, n0 + 0 = n0 <-> S n0 + 0 = S n0`{.claim}, since `n0` is arbitrary.
  - Let us consider an arbitrary `n0 : nat`{.var}.
    - Using *PeanoNat.Nat.add_succ_l*{.just} we get `forall n1 m : nat, S n1 + m = S (n1 + m)`{.claim}.
    - Using *PeanoNat.Nat.succ_inj_wd*{.just} we get `forall n1 n2 : nat, S n1 = S n2 <-> n1 = n2`{.claim}.
    - Using *RelationClasses.iff_Reflexive*{.just} we get `RelationClasses.Reflexive iff`{.claim}.
    - Using *RelationClasses.reflexivity*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x : A, R x x`{.claim}.
    - We deduce `forall x : Prop, x <-> x`{.claim}.
    - We have proved `S (n0 + 0) = S n0 <-> n0 + 0 = n0 -> Basics.flip Basics.impl (n0 + 0 = n0 <-> S (n0 + 0) = S n0) (n0 + 0 = n0 <-> n0 + 0 = n0)`{.claim}.
      - Assume `S (n0 + 0) = S n0 <-> n0 + 0 = n0`{.hyp} (lemma).
        - By *lemma*{.just} we have `S (n0 + 0) = S n0 <-> n0 + 0 = n0`{.claim}.
        - We deduce `RelationClasses.PER iff`{.claim}.
          - Using *RelationClasses.iff_equivalence*{.just} we get `RelationClasses.Equivalence iff`{.claim}.
          - Using *RelationClasses.Equivalence_PER*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R`{.claim}.
        - Using *Morphisms.trans_sym_co_inv_impl_morphism*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> forall x : A, Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)`{.claim}.

        By *firstorder*{.just} we deduce `Basics.flip Basics.impl (n0 + 0 = n0 <-> S (n0 + 0) = S n0) (n0 + 0 = n0 <-> n0 + 0 = n0)`{.claim}.
    - We have proved `S n0 + 0 = S (n0 + 0) -> Basics.flip Basics.impl (n0 + 0 = n0 <-> S n0 + 0 = S n0) (n0 + 0 = n0 <-> S (n0 + 0) = S n0)`{.claim}.
      - Assume `S n0 + 0 = S (n0 + 0)`{.hyp} (lemma).
        - In particular `Morphisms.ProperProxy eq (S n0)`, that is `S n0 = S n0`{.claim}.
          - We deduce `Morphisms.ReflexiveProxy (@eq nat)`{.claim}.
            - We deduce `RelationClasses.Reflexive (@eq nat)`{.claim}.
              - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
              - Using *RelationClasses.Equivalence_Reflexive*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R`{.claim}.
            - Using *Morphisms.reflexive_reflexive_proxy*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> Morphisms.ReflexiveProxy R`{.claim}.
          - Using *Morphisms.reflexive_proper_proxy*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), Morphisms.ReflexiveProxy R -> forall x : A, Morphisms.ProperProxy R x`{.claim}.
          - We deduce `forall x : nat, Morphisms.ProperProxy eq x`{.claim}.
        - We deduce `Morphisms.respectful eq iff (eq (S n0 + 0)) (eq (S (n0 + 0)))`, that is `forall x y : nat, x = y -> S n0 + 0 = x <-> S (n0 + 0) = y`{.claim}.
          - By *lemma*{.just} we have `S n0 + 0 = S (n0 + 0)`{.claim}.
          - We deduce `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq iff)) (@eq nat)`, that is `forall x y : nat, x = y -> Morphisms.respectful eq iff (eq x) (eq y)`{.claim}.
            - We deduce `RelationClasses.PER (@eq nat)`{.claim}.
              - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
              - Using *RelationClasses.Equivalence_PER*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R`{.claim}.
            - Using *Morphisms.PER_morphism*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful R iff)) R`{.claim}.
        - We deduce `RelationClasses.PER iff`{.claim}.
          - Using *RelationClasses.iff_equivalence*{.just} we get `RelationClasses.Equivalence iff`{.claim}.
          - Using *RelationClasses.Equivalence_PER*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R`{.claim}.
        - Using *Morphisms.trans_sym_co_inv_impl_morphism*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> forall x : A, Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)`{.claim}.

        By *congruence*{.just} we deduce `Basics.flip Basics.impl (n0 + 0 = n0 <-> S n0 + 0 = S n0) (n0 + 0 = n0 <-> S (n0 + 0) = S n0)`{.claim}.

    By *tauto*{.just} we deduce `n0 + 0 = n0 <-> S n0 + 0 = S n0`{.claim}.
- Using *PeanoNat.Nat.bi_induction*{.just} we get `forall A : nat -> Prop, Morphisms.Proper (Morphisms.respectful eq iff) A -> A 0 -> (forall n0 : nat, A n0 <-> A (S n0)) -> forall n0 : nat, A n0`{.claim}.
- By *tauto*{.just} we deduce `forall n0 : nat, n0 + 0 = n0`{.claim}.
- In particular `n + 0 = n`{.claim}.
