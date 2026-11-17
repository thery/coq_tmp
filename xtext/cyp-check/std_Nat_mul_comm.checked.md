<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# Nat.mul_comm

✅ Let `n m : nat`. We prove `n * m = m * n`.

- ✅ Thus we have `forall x y : nat, x = y -> x * m = m * x <-> y * m = m * y`.
  - ▫️ Let us choose arbitrarily `x : nat`, `y : nat`.
    - ▫️ Assume `x = y` (H).
      - ✅ In particular `Morphisms.ProperProxy eq (y * m = m * y)`, that is `(y * m = m * y) = (y * m = m * y)`.
        - ✅ Using eq_proper_proxy we get `forall (A : Type) (x0 : A), Morphisms.ProperProxy eq x0` .*by exact @Corelib.Classes.Morphisms.eq_proper_proxy*
      - ✅ In particular `y * m = m * y <-> y * m = m * y`.
        - ✅ Using iff_Reflexive we get `RelationClasses.Reflexive iff` .*by exact @Corelib.Classes.RelationClasses.iff_Reflexive*
        - ✅ Using reflexivity we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x0 : A, R x0 x0` .*by exact @Corelib.Classes.RelationClasses.reflexivity*
        - ✅ We deduce `forall x0 : Prop, x0 <-> x0`.
      - ✅ We deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (iff (x * m = m * x)) (iff (y * m = m * y))`, that is `forall x0 y0 : Prop, x0 = y0 -> Basics.flip Basics.impl (x * m = m * x <-> x0) (y * m = m * y <-> y0)`.
        - ✅ We deduce `x * m = m * x <-> y * m = m * y`.
          - ✅ We deduce `m * x = m * y`.
            - ✅ By H we have `x = y`.
            - ✅ We deduce `Morphisms.Proper (Morphisms.respectful eq eq) (Nat.mul m)`, that is `forall x0 y0 : nat, x0 = y0 -> m * x0 = m * y0`.
              - ✅ In particular `Morphisms.ProperProxy eq m`.
                - ✅ We deduce `Morphisms.ReflexiveProxy (@eq nat)`.
                  - ✅ We deduce `RelationClasses.Reflexive (@eq nat)`.
                    - ✅ Using eq_equiv we get `RelationClasses.Equivalence (@eq nat)` .*by exact @Stdlib.Arith.PeanoNat.Nat.eq_equiv*
                    - ✅ Using Equivalence_Reflexive we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R` .*by exact @Corelib.Classes.RelationClasses.Equivalence_Reflexive*
                  - ✅ Using reflexive_reflexive_proxy we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> Morphisms.ReflexiveProxy R` .*by exact @Corelib.Classes.Morphisms.reflexive_reflexive_proxy*
                - ✅ Using reflexive_proper_proxy we get `forall (A : Type) (R : Relation_Definitions.relation A), Morphisms.ReflexiveProxy R -> forall x0 : A, Morphisms.ProperProxy R x0` .*by exact @Corelib.Classes.Morphisms.reflexive_proper_proxy*
                - ✅ We deduce `forall x0 : nat, Morphisms.ProperProxy eq x0`.
              - ✅ We deduce `forall x0 : nat, Morphisms.ProperProxy eq x0 -> Morphisms.Proper (Morphisms.respectful eq eq) (Nat.mul x0)`.
                - ✅ Using mul_wd we get `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Init.Nat.mul` .*by exact @Stdlib.Arith.PeanoNat.Nat.mul_wd*
                - ✅ Using Reflexive_partial_app_morphism we get `forall (A B : Type) (R : Relation_Definitions.relation A) (R' : Relation_Definitions.relation B) (m0 : A -> B), Morphisms.Proper (Morphisms.respectful R R') m0 -> forall x0 : A, Morphisms.ProperProxy R x0 -> Morphisms.Proper R' (m0 x0)` .*by exact @Corelib.Classes.Morphisms.Reflexive_partial_app_morphism*
          - ✅ We deduce `Morphisms.respectful eq iff (eq (x * m)) (eq (y * m))`, that is `forall x0 y0 : nat, x0 = y0 -> x * m = x0 <-> y * m = y0`.
            - ✅ We deduce `x * m = y * m`.
              - ✅ In particular `Morphisms.ProperProxy eq m`, that is `m = m`.
                - ✅ We deduce `Morphisms.ReflexiveProxy (@eq nat)`.
                  - ✅ We deduce `RelationClasses.Reflexive (@eq nat)`.
                    - ✅ Using eq_equiv we get `RelationClasses.Equivalence (@eq nat)` .*by exact @Stdlib.Arith.PeanoNat.Nat.eq_equiv*
                    - ✅ Using Equivalence_Reflexive we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R` .*by exact @Corelib.Classes.RelationClasses.Equivalence_Reflexive*
                  - ✅ Using reflexive_reflexive_proxy we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> Morphisms.ReflexiveProxy R` .*by exact @Corelib.Classes.Morphisms.reflexive_reflexive_proxy*
                - ✅ Using reflexive_proper_proxy we get `forall (A : Type) (R : Relation_Definitions.relation A), Morphisms.ReflexiveProxy R -> forall x0 : A, Morphisms.ProperProxy R x0` .*by exact @Corelib.Classes.Morphisms.reflexive_proper_proxy*
                - ✅ We deduce `forall x0 : nat, Morphisms.ProperProxy eq x0`.
              - ✅ We deduce `Morphisms.respectful eq eq (Init.Nat.mul x) (Init.Nat.mul y)`, that is `forall x0 y0 : nat, x0 = y0 -> x * x0 = y * y0`.
                - ✅ By H we have `x = y`.
                - ✅ Using mul_wd we get `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Init.Nat.mul` , that is `forall x0 y0 : nat, x0 = y0 -> Morphisms.respectful eq eq (Init.Nat.mul x0) (Init.Nat.mul y0)`.*by exact @Stdlib.Arith.PeanoNat.Nat.mul_wd*
            - ❌ We deduce `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq iff)) (@eq nat)`, that is `forall x0 y0 : nat, x0 = y0 -> Morphisms.respectful eq iff (eq x0) (eq y0)`.

              <details><summary>not proved</summary>

              ```
              1 goal
                
                n, m, x, y : nat
                H : x = y
                H0 : Morphisms.ProperProxy eq (y * m = m * y)
                H1 : y * m = m * y <-> y * m = m * y
                H2 : m * x = m * y
                H3 : x * m = y * m
                H4 : RelationClasses.PER eq
                H5 :
                  forall (A : Type) (R : Relation_Definitions.relation A),
                  RelationClasses.PER R ->
                  Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful R iff)) R
                ============================
                Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq iff)) eq
              
              File "./cyp_ko_37.v", line 4, characters 0-168:
              Error: No applicable tactic.
              ```

              </details>
              - ✅ We deduce `RelationClasses.PER (@eq nat)`.
                - ✅ Using eq_equiv we get `RelationClasses.Equivalence (@eq nat)` .*by exact @Stdlib.Arith.PeanoNat.Nat.eq_equiv*
                - ✅ Using Equivalence_PER we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R` .*by exact @Corelib.Classes.RelationClasses.Equivalence_PER*
              - ✅ Using PER_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful R iff)) R` .*by exact @Corelib.Classes.Morphisms.PER_morphism*
        - ✅ We deduce `Morphisms.Proper (Morphisms.respectful iff (Morphisms.respectful eq (Basics.flip Basics.impl))) iff`, that is `forall x0 y0 : Prop, x0 <-> y0 -> Morphisms.respectful eq (Basics.flip Basics.impl) (iff x0) (iff y0)`.
          - ✅ Using iff_Transitive we get `RelationClasses.Transitive iff` .*by exact @Corelib.Classes.RelationClasses.iff_Transitive*
          - ✅ Using trans_co_eq_inv_impl_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Transitive R -> Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful eq (Basics.flip Basics.impl))) R` .*by exact @Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism*
      - ✅ We deduce `x * m = m * x <-> y * m = m * y`.
    - ✅ We have proved `x = y -> x * m = m * x <-> y * m = m * y`.
- ✅ We deduce `0 * m = m * 0`.
  - ✅ In particular `m * 0 = 0`.
    - ✅ Using mul_0_r we get `forall n0 : nat, n0 * 0 = 0` .*by exact @Stdlib.Arith.PeanoNat.Nat.mul_0_r*
  - ✅ We deduce `0 * m = 0`.
    - ✅ In particular `0 * m = 0`.
      - ✅ Using mul_0_l we get `forall n0 : nat, 0 * n0 = 0` .*by exact @Stdlib.Arith.PeanoNat.Nat.mul_0_l*
    - ✅ In particular `0 = 0`, that is `0 = 0`.
      - ✅ We deduce `RelationClasses.Reflexive (@eq nat)`.
        - ✅ Using eq_equiv we get `RelationClasses.Equivalence (@eq nat)` .*by exact @Stdlib.Arith.PeanoNat.Nat.eq_equiv*
        - ✅ Using Equivalence_Reflexive we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R` .*by exact @Corelib.Classes.RelationClasses.Equivalence_Reflexive*
      - ✅ Using reflexivity we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x : A, R x x` .*by exact @Corelib.Classes.RelationClasses.reflexivity*
      - ✅ We deduce `forall x : nat, x = x`.
    - ✅ We have proved `0 * m = 0 -> Basics.flip Basics.impl (0 * m = 0) (0 = 0)`.
      - ▫️ Assume `0 * m = 0` (lemma).
        - ✅ In particular `Morphisms.ProperProxy eq 0`, that is `0 = 0`.
          - ✅ Using eq_proper_proxy we get `forall (A : Type) (x : A), Morphisms.ProperProxy eq x` .*by exact @Corelib.Classes.Morphisms.eq_proper_proxy*
        - ✅ We deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (eq (0 * m)) (eq 0)`, that is `forall x y : nat, x = y -> Basics.flip Basics.impl (0 * m = x) (0 = y)`.
          - ✅ By lemma we have `0 * m = 0`.
          - ✅ We deduce `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq (Basics.flip Basics.impl))) (@eq nat)`, that is `forall x y : nat, x = y -> Morphisms.respectful eq (Basics.flip Basics.impl) (eq x) (eq y)`.
            - ✅ We deduce `RelationClasses.Transitive (@eq nat)`.
              - ✅ Using eq_equiv we get `RelationClasses.Equivalence (@eq nat)` .*by exact @Stdlib.Arith.PeanoNat.Nat.eq_equiv*
              - ✅ Using Equivalence_Transitive we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Transitive R` .*by exact @Corelib.Classes.RelationClasses.Equivalence_Transitive*
            - ✅ Using trans_co_eq_inv_impl_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Transitive R -> Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful eq (Basics.flip Basics.impl))) R` .*by exact @Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism*
        - ✅ We deduce `Basics.flip Basics.impl (0 * m = 0) (0 = 0)`.
  - ✅ We have proved `m * 0 = 0 -> Basics.flip Basics.impl (0 * m = m * 0) (0 * m = 0)`.
    - ▫️ Assume `m * 0 = 0` (lemma).
      - ✅ By lemma we have `m * 0 = 0`.
      - ✅ We deduce `forall x : nat, Morphisms.Proper (Morphisms.respectful eq (Basics.flip Basics.impl)) (eq x)`.
        - ✅ We deduce `RelationClasses.PER (@eq nat)`.
          - ✅ Using eq_equiv we get `RelationClasses.Equivalence (@eq nat)` .*by exact @Stdlib.Arith.PeanoNat.Nat.eq_equiv*
          - ✅ Using Equivalence_PER we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R` .*by exact @Corelib.Classes.RelationClasses.Equivalence_PER*
        - ✅ Using trans_sym_co_inv_impl_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> forall x : A, Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)` .*by exact @Corelib.Classes.Morphisms.trans_sym_co_inv_impl_morphism*
      - ✅ We deduce `Basics.flip Basics.impl (0 * m = m * 0) (0 * m = 0)`.
- ✅ We have `forall n0 : nat, n0 * m = m * n0 <-> S n0 * m = m * S n0` .*by lia*
- ✅ Using bi_induction we get `forall A : nat -> Prop, Morphisms.Proper (Morphisms.respectful eq iff) A -> A 0 -> (forall n0 : nat, A n0 <-> A (S n0)) -> forall n0 : nat, A n0` .*by exact @Stdlib.Arith.PeanoNat.Nat.bi_induction*
- ✅ We deduce `forall n0 : nat, n0 * m = m * n0`.
- ✅ In particular `n * m = m * n`.

