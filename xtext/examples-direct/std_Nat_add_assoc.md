---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# Nat.add_assoc

Let `n m p : nat`{.var}. We prove `n + (m + p) = n + m + p`{.claim}.

- Thus we have `forall x y : nat, x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p`{.claim}.
  - Let us choose arbitrarily `x : nat`{.var} and `y : nat`{.var}.
    - Assume `x = y`{.hyp} (H).
      - In particular `Morphisms.ProperProxy eq (y + (m + p) = y + m + p)`, that is `(y + (m + p) = y + m + p) = (y + (m + p) = y + m + p)`{.claim}.
        - Using *Morphisms.eq_proper_proxy*{.just} we get `forall (A : Type) (x0 : A), Morphisms.ProperProxy eq x0`{.claim}.
      - Using *RelationClasses.iff_Reflexive*{.just} we get `RelationClasses.Reflexive iff`{.claim}.
      - Using *RelationClasses.reflexivity*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x0 : A, R x0 x0`{.claim}.
      - We deduce `forall x0 : Prop, x0 <-> x0`{.claim}.
      - By *tauto*{.just} we deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (iff (x + (m + p) = x + m + p)) (iff (y + (m + p) = y + m + p))`, that is `forall x0 y0 : Prop, x0 = y0 -> Basics.flip Basics.impl (x + (m + p) = x + m + p <-> x0) (y + (m + p) = y + m + p <-> y0)`{.claim}.
        - In particular `Morphisms.ProperProxy eq p`, that is `p = p`{.claim}.
          - We deduce `Morphisms.ReflexiveProxy (@eq nat)`{.claim}.
            - We deduce `RelationClasses.Reflexive (@eq nat)`{.claim}.
              - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
              - Using *RelationClasses.Equivalence_Reflexive*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R`{.claim}.
            - Using *Morphisms.reflexive_reflexive_proxy*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> Morphisms.ReflexiveProxy R`{.claim}.
          - Using *Morphisms.reflexive_proper_proxy*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), Morphisms.ReflexiveProxy R -> forall x0 : A, Morphisms.ProperProxy R x0`{.claim}.
          - We deduce `forall x0 : nat, Morphisms.ProperProxy eq x0`{.claim}.
        - By *tauto*{.just} we deduce `Morphisms.respectful eq eq (Init.Nat.add (x + m)) (Init.Nat.add (y + m))`, that is `forall x0 y0 : nat, x0 = y0 -> x + m + x0 = y + m + y0`{.claim}.
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
          - Using *PeanoNat.Nat.add_wd*{.just} we get `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Init.Nat.add`, that is `forall x0 y0 : nat, x0 = y0 -> Morphisms.respectful eq eq (Init.Nat.add x0) (Init.Nat.add y0)`{.claim}.
        - By *tauto*{.just} we deduce `Morphisms.respectful eq iff (eq (x + (m + p))) (eq (y + (m + p)))`, that is `forall x0 y0 : nat, x0 = y0 -> x + (m + p) = x0 <-> y + (m + p) = y0`{.claim}.
          - In particular `Morphisms.ProperProxy eq (m + p)`, that is `m + p = m + p`{.claim}.
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

      By *lia*{.just} we deduce `x + (m + p) = x + m + p <-> y + (m + p) = y + m + p`{.claim}.

    We have proved `x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p`{.claim}.
- Using *PeanoNat.Nat.add_0_l*{.just} we get `forall n0 : nat, 0 + n0 = n0`{.claim}.
- Using *PeanoNat.Nat.add_0_l*{.just} we get `forall n0 : nat, 0 + n0 = n0`{.claim}.
- In particular `m + p = m + p`, that is `m + p = m + p`{.claim}.
  - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
  - Using *RelationClasses.Equivalence_Reflexive*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R`{.claim}.
  - Using *RelationClasses.reflexivity*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x : A, R x x`{.claim}.
  - By *tauto*{.just} we deduce `forall x : nat, x = x`{.claim}.
- We have proved `0 + m = m -> Basics.flip Basics.impl (m + p = 0 + m + p) (m + p = m + p)`{.claim}.
  - Assume `0 + m = m`{.hyp} (lemma).
    - In particular `Morphisms.ProperProxy eq p`, that is `p = p`{.claim}.
      - We deduce `Morphisms.ReflexiveProxy (@eq nat)`{.claim}.
        - We deduce `RelationClasses.Reflexive (@eq nat)`{.claim}.
          - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
          - Using *RelationClasses.Equivalence_Reflexive*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R`{.claim}.
        - Using *Morphisms.reflexive_reflexive_proxy*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> Morphisms.ReflexiveProxy R`{.claim}.
      - Using *Morphisms.reflexive_proper_proxy*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), Morphisms.ReflexiveProxy R -> forall x : A, Morphisms.ProperProxy R x`{.claim}.
      - We deduce `forall x : nat, Morphisms.ProperProxy eq x`{.claim}.
    - We deduce `Morphisms.respectful eq eq (Init.Nat.add (0 + m)) (Init.Nat.add m)`, that is `forall x y : nat, x = y -> 0 + m + x = m + y`{.claim}.
      - By *lemma*{.just} we have `0 + m = m`{.claim}.
      - Using *PeanoNat.Nat.add_wd*{.just} we get `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Init.Nat.add`, that is `forall x y : nat, x = y -> Morphisms.respectful eq eq (Init.Nat.add x) (Init.Nat.add y)`{.claim}.
    - We deduce `RelationClasses.PER (@eq nat)`{.claim}.
      - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
      - Using *RelationClasses.Equivalence_PER*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R`{.claim}.
    - Using *Morphisms.trans_sym_co_inv_impl_morphism*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> forall x : A, Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)`{.claim}.

    By *congruence*{.just} we deduce `Basics.flip Basics.impl (m + p = 0 + m + p) (m + p = m + p)`{.claim}.
- We have proved `0 + (m + p) = m + p -> Basics.flip Basics.impl (0 + (m + p) = 0 + m + p) (m + p = 0 + m + p)`{.claim}.
  - Assume `0 + (m + p) = m + p`{.hyp} (lemma).
    - In particular `Morphisms.ProperProxy eq (0 + m + p)`, that is `0 + m + p = 0 + m + p`{.claim}.
      - Using *Morphisms.eq_proper_proxy*{.just} we get `forall (A : Type) (x : A), Morphisms.ProperProxy eq x`{.claim}.
    - We deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (eq (0 + (m + p))) (eq (m + p))`, that is `forall x y : nat, x = y -> Basics.flip Basics.impl (0 + (m + p) = x) (m + p = y)`{.claim}.
      - By *lemma*{.just} we have `0 + (m + p) = m + p`{.claim}.
      - We deduce `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq (Basics.flip Basics.impl))) (@eq nat)`, that is `forall x y : nat, x = y -> Morphisms.respectful eq (Basics.flip Basics.impl) (eq x) (eq y)`{.claim}.
        - We deduce `RelationClasses.Transitive (@eq nat)`{.claim}.
          - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
          - Using *RelationClasses.Equivalence_Transitive*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Transitive R`{.claim}.
        - Using *Morphisms.trans_co_eq_inv_impl_morphism*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Transitive R -> Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful eq (Basics.flip Basics.impl))) R`{.claim}.

    We deduce `Basics.flip Basics.impl (0 + (m + p) = 0 + m + p) (m + p = 0 + m + p)`{.claim}.
- By *lia*{.just} we have `forall n0 : nat, n0 + (m + p) = n0 + m + p <-> S n0 + (m + p) = S n0 + m + p`{.claim}.
- Using *PeanoNat.Nat.bi_induction*{.just} we get `forall A : nat -> Prop, Morphisms.Proper (Morphisms.respectful eq iff) A -> A 0 -> (forall n0 : nat, A n0 <-> A (S n0)) -> forall n0 : nat, A n0`{.claim}.
- By *lia*{.just} we deduce `forall n0 : nat, n0 + (m + p) = n0 + m + p`{.claim}.
- In particular `n + (m + p) = n + m + p`{.claim}.
