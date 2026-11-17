<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# Nat.add_assoc

✅ Let `n m p : nat`. We prove `n + (m + p) = n + m + p`.

- ✅ Thus we have `forall x y : nat, x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p`.
  - ▫️ Let us choose arbitrarily `x : nat`, `y : nat`.
    - ▫️ Assume `x = y` (H).
      - ✅ In particular `Morphisms.ProperProxy eq (y + (m + p) = y + m + p)`, that is `(y + (m + p) = y + m + p) = (y + (m + p) = y + m + p)`.
        - ✅ Using eq_proper_proxy we get `forall (A : Type) (x0 : A), Morphisms.ProperProxy eq x0` .*by exact @Corelib.Classes.Morphisms.eq_proper_proxy*
      - ✅ In particular `y + (m + p) = y + m + p <-> y + (m + p) = y + m + p`.
        - ✅ Using iff_Reflexive we get `RelationClasses.Reflexive iff` .*by exact @Corelib.Classes.RelationClasses.iff_Reflexive*
        - ✅ Using reflexivity we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x0 : A, R x0 x0` .*by exact @Corelib.Classes.RelationClasses.reflexivity*
        - ✅ We deduce `forall x0 : Prop, x0 <-> x0`.
      - ✅ We deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (iff (x + (m + p) = x + m + p)) (iff (y + (m + p) = y + m + p))`, that is `forall x0 y0 : Prop, x0 = y0 -> Basics.flip Basics.impl (x + (m + p) = x + m + p <-> x0) (y + (m + p) = y + m + p <-> y0)`.
        - ✅ We deduce `x + (m + p) = x + m + p <-> y + (m + p) = y + m + p`.
          - ✅ We deduce `x + m + p = y + m + p`.
            - ✅ In particular `Morphisms.ProperProxy eq p`, that is `p = p`.
              - ✅ We deduce `Morphisms.ReflexiveProxy (@eq nat)`.
                - ✅ We deduce `RelationClasses.Reflexive (@eq nat)`.
                  - ✅ Using eq_equiv we get `RelationClasses.Equivalence (@eq nat)` .*by exact @Stdlib.Arith.PeanoNat.Nat.eq_equiv*
                  - ✅ Using Equivalence_Reflexive we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R` .*by exact @Corelib.Classes.RelationClasses.Equivalence_Reflexive*
                - ✅ Using reflexive_reflexive_proxy we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> Morphisms.ReflexiveProxy R` .*by exact @Corelib.Classes.Morphisms.reflexive_reflexive_proxy*
              - ✅ Using reflexive_proper_proxy we get `forall (A : Type) (R : Relation_Definitions.relation A), Morphisms.ReflexiveProxy R -> forall x0 : A, Morphisms.ProperProxy R x0` .*by exact @Corelib.Classes.Morphisms.reflexive_proper_proxy*
              - ✅ We deduce `forall x0 : nat, Morphisms.ProperProxy eq x0`.
            - ✅ We deduce `Morphisms.respectful eq eq (Init.Nat.add (x + m)) (Init.Nat.add (y + m))`, that is `forall x0 y0 : nat, x0 = y0 -> x + m + x0 = y + m + y0`.
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
              - ✅ Using add_wd we get `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Init.Nat.add` , that is `forall x0 y0 : nat, x0 = y0 -> Morphisms.respectful eq eq (Init.Nat.add x0) (Init.Nat.add y0)`.*by exact @Stdlib.Arith.PeanoNat.Nat.add_wd*
          - ✅ We deduce `Morphisms.respectful eq iff (eq (x + (m + p))) (eq (y + (m + p)))`, that is `forall x0 y0 : nat, x0 = y0 -> x + (m + p) = x0 <-> y + (m + p) = y0`.
            - ✅ We deduce `x + (m + p) = y + (m + p)`.
              - ✅ In particular `Morphisms.ProperProxy eq (m + p)`, that is `m + p = m + p`.
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
                
                n, m, p, x, y : nat
                H : x = y
                H0 : Morphisms.ProperProxy eq (y + (m + p) = y + m + p)
                H1 : y + (m + p) = y + m + p <-> y + (m + p) = y + m + p
                H2 : x + m + p = y + m + p
                H3 : x + (m + p) = y + (m + p)
                H4 : RelationClasses.PER eq
                H5 :
                  forall (A : Type) (R : Relation_Definitions.relation A),
                  RelationClasses.PER R ->
                  Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful R iff)) R
                ============================
                Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq iff)) eq
              
              File "./cyp_ko_46.v", line 4, characters 0-168:
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
      - ✅ We deduce `x + (m + p) = x + m + p <-> y + (m + p) = y + m + p`.
    - ✅ We have proved `x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p`.
- ✅ We deduce `0 + (m + p) = 0 + m + p`.
  - ✅ In particular `0 + (m + p) = m + p`.
    - ✅ Using add_0_l we get `forall n0 : nat, 0 + n0 = n0` .*by exact @Stdlib.Arith.PeanoNat.Nat.add_0_l*
  - ✅ We deduce `m + p = 0 + m + p`.
    - ✅ In particular `0 + m = m`.
      - ✅ Using add_0_l we get `forall n0 : nat, 0 + n0 = n0` .*by exact @Stdlib.Arith.PeanoNat.Nat.add_0_l*
    - ✅ In particular `m + p = m + p`, that is `m + p = m + p`.
      - ✅ We deduce `RelationClasses.Reflexive (@eq nat)`.
        - ✅ Using eq_equiv we get `RelationClasses.Equivalence (@eq nat)` .*by exact @Stdlib.Arith.PeanoNat.Nat.eq_equiv*
        - ✅ Using Equivalence_Reflexive we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R` .*by exact @Corelib.Classes.RelationClasses.Equivalence_Reflexive*
      - ✅ Using reflexivity we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x : A, R x x` .*by exact @Corelib.Classes.RelationClasses.reflexivity*
      - ✅ We deduce `forall x : nat, x = x`.
    - ✅ We have proved `0 + m = m -> Basics.flip Basics.impl (m + p = 0 + m + p) (m + p = m + p)`.
      - ▫️ Assume `0 + m = m` (lemma).
        - ✅ We deduce `0 + m + p = m + p`.
          - ✅ In particular `Morphisms.ProperProxy eq p`, that is `p = p`.
            - ✅ We deduce `Morphisms.ReflexiveProxy (@eq nat)`.
              - ✅ We deduce `RelationClasses.Reflexive (@eq nat)`.
                - ✅ Using eq_equiv we get `RelationClasses.Equivalence (@eq nat)` .*by exact @Stdlib.Arith.PeanoNat.Nat.eq_equiv*
                - ✅ Using Equivalence_Reflexive we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R` .*by exact @Corelib.Classes.RelationClasses.Equivalence_Reflexive*
              - ✅ Using reflexive_reflexive_proxy we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> Morphisms.ReflexiveProxy R` .*by exact @Corelib.Classes.Morphisms.reflexive_reflexive_proxy*
            - ✅ Using reflexive_proper_proxy we get `forall (A : Type) (R : Relation_Definitions.relation A), Morphisms.ReflexiveProxy R -> forall x : A, Morphisms.ProperProxy R x` .*by exact @Corelib.Classes.Morphisms.reflexive_proper_proxy*
            - ✅ We deduce `forall x : nat, Morphisms.ProperProxy eq x`.
          - ✅ We deduce `Morphisms.respectful eq eq (Init.Nat.add (0 + m)) (Init.Nat.add m)`, that is `forall x y : nat, x = y -> 0 + m + x = m + y`.
            - ✅ By lemma we have `0 + m = m`.
            - ✅ Using add_wd we get `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Init.Nat.add` , that is `forall x y : nat, x = y -> Morphisms.respectful eq eq (Init.Nat.add x) (Init.Nat.add y)`.*by exact @Stdlib.Arith.PeanoNat.Nat.add_wd*
        - ✅ We deduce `forall x : nat, Morphisms.Proper (Morphisms.respectful eq (Basics.flip Basics.impl)) (eq x)`.
          - ✅ We deduce `RelationClasses.PER (@eq nat)`.
            - ✅ Using eq_equiv we get `RelationClasses.Equivalence (@eq nat)` .*by exact @Stdlib.Arith.PeanoNat.Nat.eq_equiv*
            - ✅ Using Equivalence_PER we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R` .*by exact @Corelib.Classes.RelationClasses.Equivalence_PER*
          - ✅ Using trans_sym_co_inv_impl_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> forall x : A, Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)` .*by exact @Corelib.Classes.Morphisms.trans_sym_co_inv_impl_morphism*
        - ✅ We deduce `Basics.flip Basics.impl (m + p = 0 + m + p) (m + p = m + p)`.
  - ✅ We have proved `0 + (m + p) = m + p -> Basics.flip Basics.impl (0 + (m + p) = 0 + m + p) (m + p = 0 + m + p)`.
    - ▫️ Assume `0 + (m + p) = m + p` (lemma).
      - ✅ In particular `Morphisms.ProperProxy eq (0 + m + p)`, that is `0 + m + p = 0 + m + p`.
        - ✅ Using eq_proper_proxy we get `forall (A : Type) (x : A), Morphisms.ProperProxy eq x` .*by exact @Corelib.Classes.Morphisms.eq_proper_proxy*
      - ✅ We deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (eq (0 + (m + p))) (eq (m + p))`, that is `forall x y : nat, x = y -> Basics.flip Basics.impl (0 + (m + p) = x) (m + p = y)`.
        - ✅ By lemma we have `0 + (m + p) = m + p`.
        - ✅ We deduce `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq (Basics.flip Basics.impl))) (@eq nat)`, that is `forall x y : nat, x = y -> Morphisms.respectful eq (Basics.flip Basics.impl) (eq x) (eq y)`.
          - ✅ We deduce `RelationClasses.Transitive (@eq nat)`.
            - ✅ Using eq_equiv we get `RelationClasses.Equivalence (@eq nat)` .*by exact @Stdlib.Arith.PeanoNat.Nat.eq_equiv*
            - ✅ Using Equivalence_Transitive we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Transitive R` .*by exact @Corelib.Classes.RelationClasses.Equivalence_Transitive*
          - ✅ Using trans_co_eq_inv_impl_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Transitive R -> Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful eq (Basics.flip Basics.impl))) R` .*by exact @Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism*
      - ✅ We deduce `Basics.flip Basics.impl (0 + (m + p) = 0 + m + p) (m + p = 0 + m + p)`.
- ✅ We have `forall n0 : nat, n0 + (m + p) = n0 + m + p <-> S n0 + (m + p) = S n0 + m + p` .*by lia*
- ✅ Using bi_induction we get `forall A : nat -> Prop, Morphisms.Proper (Morphisms.respectful eq iff) A -> A 0 -> (forall n0 : nat, A n0 <-> A (S n0)) -> forall n0 : nat, A n0` .*by exact @Stdlib.Arith.PeanoNat.Nat.bi_induction*
- ✅ We deduce `forall n0 : nat, n0 + (m + p) = n0 + m + p`.
- ✅ In particular `n + (m + p) = n + m + p`.

