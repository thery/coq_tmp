<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# Nat.add_succ_r

✅ Let `n m : nat`. We prove `n + S m = S (n + m)`.

- ✅ Thus we have `forall x y : nat, x = y -> x + S m = S (x + m) <-> y + S m = S (y + m)`.
  - ▫️ Let us choose arbitrarily `x : nat`, `y : nat`.
    - ▫️ Assume `x = y` (H).
      - ✅ In particular `Morphisms.ProperProxy eq (y + S m = S (y + m))`, that is `(y + S m = S (y + m)) = (y + S m = S (y + m))`.
        - ✅ Using eq_proper_proxy we get `forall (A : Type) (x0 : A), Morphisms.ProperProxy eq x0` .*by exact @Corelib.Classes.Morphisms.eq_proper_proxy*
      - ✅ In particular `y + S m = S (y + m) <-> y + S m = S (y + m)`.
        - ✅ Using iff_Reflexive we get `RelationClasses.Reflexive iff` .*by exact @Corelib.Classes.RelationClasses.iff_Reflexive*
        - ✅ Using reflexivity we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x0 : A, R x0 x0` .*by exact @Corelib.Classes.RelationClasses.reflexivity*
        - ✅ We deduce `forall x0 : Prop, x0 <-> x0`.
      - ✅ We deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (iff (x + S m = S (x + m))) (iff (y + S m = S (y + m)))`, that is `forall x0 y0 : Prop, x0 = y0 -> Basics.flip Basics.impl (x + S m = S (x + m) <-> x0) (y + S m = S (y + m) <-> y0)`.
        - ✅ We deduce `x + S m = S (x + m) <-> y + S m = S (y + m)`.
          - ✅ We deduce `S (x + m) = S (y + m)`.
            - ✅ We deduce `x + m = y + m`.
              - ✅ In particular `Morphisms.ProperProxy eq m`, that is `m = m`.
                - ✅ We deduce `Morphisms.ReflexiveProxy (@eq nat)`.
                  - ✅ We deduce `RelationClasses.Reflexive (@eq nat)`.
                    - ✅ Using eq_equiv we get `RelationClasses.Equivalence (@eq nat)` .*by exact @Stdlib.Arith.PeanoNat.Nat.eq_equiv*
                    - ✅ Using Equivalence_Reflexive we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R` .*by exact @Corelib.Classes.RelationClasses.Equivalence_Reflexive*
                  - ✅ Using reflexive_reflexive_proxy we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> Morphisms.ReflexiveProxy R` .*by exact @Corelib.Classes.Morphisms.reflexive_reflexive_proxy*
                - ✅ Using reflexive_proper_proxy we get `forall (A : Type) (R : Relation_Definitions.relation A), Morphisms.ReflexiveProxy R -> forall x0 : A, Morphisms.ProperProxy R x0` .*by exact @Corelib.Classes.Morphisms.reflexive_proper_proxy*
                - ✅ We deduce `forall x0 : nat, Morphisms.ProperProxy eq x0`.
              - ✅ We deduce `Morphisms.respectful eq eq (Init.Nat.add x) (Init.Nat.add y)`, that is `forall x0 y0 : nat, x0 = y0 -> x + x0 = y + y0`.
                - ✅ By H we have `x = y`.
                - ✅ Using add_wd we get `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Init.Nat.add` , that is `forall x0 y0 : nat, x0 = y0 -> Morphisms.respectful eq eq (Init.Nat.add x0) (Init.Nat.add y0)`.*by exact @Stdlib.Arith.PeanoNat.Nat.add_wd*
            - ✅ Using succ_wd we get `Morphisms.Proper (Morphisms.respectful eq eq) S` , that is `forall x0 y0 : nat, x0 = y0 -> S x0 = S y0`.*by exact @Stdlib.Arith.PeanoNat.Nat.succ_wd*
          - ✅ We deduce `Morphisms.respectful eq iff (eq (x + S m)) (eq (y + S m))`, that is `forall x0 y0 : nat, x0 = y0 -> x + S m = x0 <-> y + S m = y0`.
            - ✅ We deduce `x + S m = y + S m`.
              - ✅ In particular `Morphisms.ProperProxy eq (S m)`, that is `S m = S m`.
                - ✅ We deduce `Morphisms.ReflexiveProxy (@eq nat)`.
                  - ✅ We deduce `RelationClasses.Reflexive (@eq nat)`.
                    - ✅ Using eq_equiv we get `RelationClasses.Equivalence (@eq nat)` .*by exact @Stdlib.Arith.PeanoNat.Nat.eq_equiv*
                    - ✅ Using Equivalence_Reflexive we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R` .*by exact @Corelib.Classes.RelationClasses.Equivalence_Reflexive*
                  - ✅ Using reflexive_reflexive_proxy we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> Morphisms.ReflexiveProxy R` .*by exact @Corelib.Classes.Morphisms.reflexive_reflexive_proxy*
                - ✅ Using reflexive_proper_proxy we get `forall (A : Type) (R : Relation_Definitions.relation A), Morphisms.ReflexiveProxy R -> forall x0 : A, Morphisms.ProperProxy R x0` .*by exact @Corelib.Classes.Morphisms.reflexive_proper_proxy*
                - ✅ We deduce `forall x0 : nat, Morphisms.ProperProxy eq x0`.
              - ✅ We deduce `Morphisms.respectful eq eq (Init.Nat.add x) (Init.Nat.add y)`, that is `forall x0 y0 : nat, x0 = y0 -> x + x0 = y + y0`.
                - ✅ By H we have `x = y`.
                - ✅ Using add_wd we get `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Init.Nat.add` , that is `forall x0 y0 : nat, x0 = y0 -> Morphisms.respectful eq eq (Init.Nat.add x0) (Init.Nat.add y0)`.*by exact @Stdlib.Arith.PeanoNat.Nat.add_wd*
            - ❌ We deduce `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq iff)) (@eq nat)`, that is `forall x0 y0 : nat, x0 = y0 -> Morphisms.respectful eq iff (eq x0) (eq y0)`.

              <details><summary>not proved</summary>

              ```
              1 goal
                
                n, m, x, y : nat
                H : x = y
                H0 : Morphisms.ProperProxy eq (y + S m = S (y + m))
                H1 : y + S m = S (y + m) <-> y + S m = S (y + m)
                H2 : S (x + m) = S (y + m)
                H3 : x + S m = y + S m
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
      - ✅ We deduce `x + S m = S (x + m) <-> y + S m = S (y + m)`.
    - ✅ We have proved `x = y -> x + S m = S (x + m) <-> y + S m = S (y + m)`.
- ✅ We deduce `0 + S m = S (0 + m)`.
  - ✅ In particular `0 + S m = S m`.
    - ✅ Using add_0_l we get `forall n0 : nat, 0 + n0 = n0` .*by exact @Stdlib.Arith.PeanoNat.Nat.add_0_l*
  - ✅ We deduce `S m = S (0 + m)`.
    - ✅ In particular `0 + m = m`.
      - ✅ Using add_0_l we get `forall n0 : nat, 0 + n0 = n0` .*by exact @Stdlib.Arith.PeanoNat.Nat.add_0_l*
    - ✅ In particular `S m = S m`, that is `S m = S m`.
      - ✅ We deduce `RelationClasses.Reflexive (@eq nat)`.
        - ✅ Using eq_equiv we get `RelationClasses.Equivalence (@eq nat)` .*by exact @Stdlib.Arith.PeanoNat.Nat.eq_equiv*
        - ✅ Using Equivalence_Reflexive we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R` .*by exact @Corelib.Classes.RelationClasses.Equivalence_Reflexive*
      - ✅ Using reflexivity we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x : A, R x x` .*by exact @Corelib.Classes.RelationClasses.reflexivity*
      - ✅ We deduce `forall x : nat, x = x`.
    - ✅ We have proved `0 + m = m -> Basics.flip Basics.impl (S m = S (0 + m)) (S m = S m)`.
      - ▫️ Assume `0 + m = m` (lemma).
        - ✅ We deduce `S (0 + m) = S m`.
          - ✅ By lemma we have `0 + m = m`.
          - ✅ Using succ_wd we get `Morphisms.Proper (Morphisms.respectful eq eq) S` , that is `forall x y : nat, x = y -> S x = S y`.*by exact @Stdlib.Arith.PeanoNat.Nat.succ_wd*
        - ✅ We deduce `forall x : nat, Morphisms.Proper (Morphisms.respectful eq (Basics.flip Basics.impl)) (eq x)`.
          - ✅ We deduce `RelationClasses.PER (@eq nat)`.
            - ✅ Using eq_equiv we get `RelationClasses.Equivalence (@eq nat)` .*by exact @Stdlib.Arith.PeanoNat.Nat.eq_equiv*
            - ✅ Using Equivalence_PER we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R` .*by exact @Corelib.Classes.RelationClasses.Equivalence_PER*
          - ✅ Using trans_sym_co_inv_impl_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> forall x : A, Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)` .*by exact @Corelib.Classes.Morphisms.trans_sym_co_inv_impl_morphism*
        - ✅ We deduce `Basics.flip Basics.impl (S m = S (0 + m)) (S m = S m)`.
  - ✅ We have proved `0 + S m = S m -> Basics.flip Basics.impl (0 + S m = S (0 + m)) (S m = S (0 + m))`.
    - ▫️ Assume `0 + S m = S m` (lemma).
      - ✅ In particular `Morphisms.ProperProxy eq (S (0 + m))`, that is `S (0 + m) = S (0 + m)`.
        - ✅ Using eq_proper_proxy we get `forall (A : Type) (x : A), Morphisms.ProperProxy eq x` .*by exact @Corelib.Classes.Morphisms.eq_proper_proxy*
      - ✅ We deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (eq (0 + S m)) (eq (S m))`, that is `forall x y : nat, x = y -> Basics.flip Basics.impl (0 + S m = x) (S m = y)`.
        - ✅ By lemma we have `0 + S m = S m`.
        - ✅ We deduce `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq (Basics.flip Basics.impl))) (@eq nat)`, that is `forall x y : nat, x = y -> Morphisms.respectful eq (Basics.flip Basics.impl) (eq x) (eq y)`.
          - ✅ We deduce `RelationClasses.Transitive (@eq nat)`.
            - ✅ Using eq_equiv we get `RelationClasses.Equivalence (@eq nat)` .*by exact @Stdlib.Arith.PeanoNat.Nat.eq_equiv*
            - ✅ Using Equivalence_Transitive we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Transitive R` .*by exact @Corelib.Classes.RelationClasses.Equivalence_Transitive*
          - ✅ Using trans_co_eq_inv_impl_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Transitive R -> Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful eq (Basics.flip Basics.impl))) R` .*by exact @Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism*
      - ✅ We deduce `Basics.flip Basics.impl (0 + S m = S (0 + m)) (S m = S (0 + m))`.
- ✅ We have `forall n0 : nat, n0 + S m = S (n0 + m) <-> S n0 + S m = S (S n0 + m)` .*by lia*
- ✅ Using bi_induction we get `forall A : nat -> Prop, Morphisms.Proper (Morphisms.respectful eq iff) A -> A 0 -> (forall n0 : nat, A n0 <-> A (S n0)) -> forall n0 : nat, A n0` .*by exact @Stdlib.Arith.PeanoNat.Nat.bi_induction*
- ✅ We deduce `forall n0 : nat, n0 + S m = S (n0 + m)`.
- ✅ In particular `n + S m = S (n + m)`.

