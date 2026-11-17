<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# Nat.add_0_r

✅ Let `n : nat`. We prove `n + 0 = n`.

- ✅ Thus we have `forall x y : nat, x = y -> x + 0 = x <-> y + 0 = y`.
  - ▫️ Let us choose arbitrarily `x : nat`, `y : nat`.
    - ▫️ Assume `x = y` (H).
      - ✅ In particular `Morphisms.ProperProxy eq (y + 0 = y)`, that is `(y + 0 = y) = (y + 0 = y)`.
        - ✅ Using eq_proper_proxy we get `forall (A : Type) (x0 : A), Morphisms.ProperProxy eq x0` .*by exact @Corelib.Classes.Morphisms.eq_proper_proxy*
      - ✅ In particular `y + 0 = y <-> y + 0 = y`.
        - ✅ Using iff_Reflexive we get `RelationClasses.Reflexive iff` .*by exact @Corelib.Classes.RelationClasses.iff_Reflexive*
        - ✅ Using reflexivity we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x0 : A, R x0 x0` .*by exact @Corelib.Classes.RelationClasses.reflexivity*
        - ✅ We deduce `forall x0 : Prop, x0 <-> x0`.
      - ✅ We deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (iff (x + 0 = x)) (iff (y + 0 = y))`, that is `forall x0 y0 : Prop, x0 = y0 -> Basics.flip Basics.impl (x + 0 = x <-> x0) (y + 0 = y <-> y0)`.
        - ✅ We deduce `x + 0 = x <-> y + 0 = y`.
          - ✅ By H we have `x = y`.
          - ✅ We deduce `Morphisms.respectful eq iff (eq (x + 0)) (eq (y + 0))`, that is `forall x0 y0 : nat, x0 = y0 -> x + 0 = x0 <-> y + 0 = y0`.
            - ✅ We deduce `x + 0 = y + 0`.
              - ✅ In particular `Morphisms.ProperProxy eq 0`, that is `0 = 0`.
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
                
                n, x, y : nat
                H : x = y
                H0 : Morphisms.ProperProxy eq (y + 0 = y)
                H1 : y + 0 = y <-> y + 0 = y
                H2 : x = y
                H3 : x + 0 = y + 0
                H4 : RelationClasses.PER eq
                H5 :
                  forall (A : Type) (R : Relation_Definitions.relation A),
                  RelationClasses.PER R ->
                  Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful R iff)) R
                ============================
                Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq iff)) eq
              
              File "./cyp_ko_24.v", line 4, characters 0-168:
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
      - ✅ We deduce `x + 0 = x <-> y + 0 = y`.
    - ✅ We have proved `x = y -> x + 0 = x <-> y + 0 = y`.
- ✅ We deduce `0 + 0 = 0`.
  - ✅ In particular `0 + 0 = 0`.
    - ✅ Using add_0_l we get `forall n0 : nat, 0 + n0 = n0` .*by exact @Stdlib.Arith.PeanoNat.Nat.add_0_l*
  - ✅ In particular `0 = 0`, that is `0 = 0`.
    - ✅ We deduce `RelationClasses.Reflexive (@eq nat)`.
      - ✅ Using eq_equiv we get `RelationClasses.Equivalence (@eq nat)` .*by exact @Stdlib.Arith.PeanoNat.Nat.eq_equiv*
      - ✅ Using Equivalence_Reflexive we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R` .*by exact @Corelib.Classes.RelationClasses.Equivalence_Reflexive*
    - ✅ Using reflexivity we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x : A, R x x` .*by exact @Corelib.Classes.RelationClasses.reflexivity*
    - ✅ We deduce `forall x : nat, x = x`.
  - ✅ We have proved `0 + 0 = 0 -> Basics.flip Basics.impl (0 + 0 = 0) (0 = 0)`.
    - ▫️ Assume `0 + 0 = 0` (lemma).
      - ✅ In particular `Morphisms.ProperProxy eq 0`, that is `0 = 0`.
        - ✅ Using eq_proper_proxy we get `forall (A : Type) (x : A), Morphisms.ProperProxy eq x` .*by exact @Corelib.Classes.Morphisms.eq_proper_proxy*
      - ✅ We deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (eq (0 + 0)) (eq 0)`, that is `forall x y : nat, x = y -> Basics.flip Basics.impl (0 + 0 = x) (0 = y)`.
        - ✅ By lemma we have `0 + 0 = 0`.
        - ✅ We deduce `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq (Basics.flip Basics.impl))) (@eq nat)`, that is `forall x y : nat, x = y -> Morphisms.respectful eq (Basics.flip Basics.impl) (eq x) (eq y)`.
          - ✅ We deduce `RelationClasses.Transitive (@eq nat)`.
            - ✅ Using eq_equiv we get `RelationClasses.Equivalence (@eq nat)` .*by exact @Stdlib.Arith.PeanoNat.Nat.eq_equiv*
            - ✅ Using Equivalence_Transitive we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Transitive R` .*by exact @Corelib.Classes.RelationClasses.Equivalence_Transitive*
          - ✅ Using trans_co_eq_inv_impl_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Transitive R -> Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful eq (Basics.flip Basics.impl))) R` .*by exact @Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism*
      - ✅ We deduce `Basics.flip Basics.impl (0 + 0 = 0) (0 = 0)`.
- ✅ We have `forall n0 : nat, n0 + 0 = n0 <-> S n0 + 0 = S n0`, since `n0` is arbitrary.
  - ▫️ Let us consider an arbitrary `n0 : nat`.
    - ✅ In particular `S n0 + 0 = S (n0 + 0)`.
      - ✅ Using add_succ_l we get `forall n1 m : nat, S n1 + m = S (n1 + m)` .*by exact @Stdlib.Arith.PeanoNat.Nat.add_succ_l*
    - ✅ We deduce `n0 + 0 = n0 <-> S (n0 + 0) = S n0`.
      - ✅ In particular `S (n0 + 0) = S n0 <-> n0 + 0 = n0`.
        - ✅ Using succ_inj_wd we get `forall n1 n2 : nat, S n1 = S n2 <-> n1 = n2` .*by exact @Stdlib.Arith.PeanoNat.Nat.succ_inj_wd*
      - ✅ In particular `n0 + 0 = n0 <-> n0 + 0 = n0`.
        - ✅ Using iff_Reflexive we get `RelationClasses.Reflexive iff` .*by exact @Corelib.Classes.RelationClasses.iff_Reflexive*
        - ✅ Using reflexivity we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x : A, R x x` .*by exact @Corelib.Classes.RelationClasses.reflexivity*
        - ✅ We deduce `forall x : Prop, x <-> x`.
      - ✅ We have proved `S (n0 + 0) = S n0 <-> n0 + 0 = n0 -> Basics.flip Basics.impl (n0 + 0 = n0 <-> S (n0 + 0) = S n0) (n0 + 0 = n0 <-> n0 + 0 = n0)`.
        - ▫️ Assume `S (n0 + 0) = S n0 <-> n0 + 0 = n0` (lemma).
          - ✅ By lemma we have `S (n0 + 0) = S n0 <-> n0 + 0 = n0`.
          - ✅ We deduce `forall x : Prop, Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (iff x)`.
            - ✅ We deduce `RelationClasses.PER iff`.
              - ✅ Using iff_equivalence we get `RelationClasses.Equivalence iff` .*by exact @Corelib.Classes.RelationClasses.iff_equivalence*
              - ✅ Using Equivalence_PER we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R` .*by exact @Corelib.Classes.RelationClasses.Equivalence_PER*
            - ✅ Using trans_sym_co_inv_impl_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> forall x : A, Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)` .*by exact @Corelib.Classes.Morphisms.trans_sym_co_inv_impl_morphism*
          - ✅ We deduce `Basics.flip Basics.impl (n0 + 0 = n0 <-> S (n0 + 0) = S n0) (n0 + 0 = n0 <-> n0 + 0 = n0)`.
    - ✅ We have proved `S n0 + 0 = S (n0 + 0) -> Basics.flip Basics.impl (n0 + 0 = n0 <-> S n0 + 0 = S n0) (n0 + 0 = n0 <-> S (n0 + 0) = S n0)`.
      - ▫️ Assume `S n0 + 0 = S (n0 + 0)` (lemma).
        - ✅ We deduce `S n0 + 0 = S n0 <-> S (n0 + 0) = S n0`.
          - ✅ In particular `Morphisms.ProperProxy eq (S n0)`, that is `S n0 = S n0`.
            - ✅ We deduce `Morphisms.ReflexiveProxy (@eq nat)`.
              - ✅ We deduce `RelationClasses.Reflexive (@eq nat)`.
                - ✅ Using eq_equiv we get `RelationClasses.Equivalence (@eq nat)` .*by exact @Stdlib.Arith.PeanoNat.Nat.eq_equiv*
                - ✅ Using Equivalence_Reflexive we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R` .*by exact @Corelib.Classes.RelationClasses.Equivalence_Reflexive*
              - ✅ Using reflexive_reflexive_proxy we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> Morphisms.ReflexiveProxy R` .*by exact @Corelib.Classes.Morphisms.reflexive_reflexive_proxy*
            - ✅ Using reflexive_proper_proxy we get `forall (A : Type) (R : Relation_Definitions.relation A), Morphisms.ReflexiveProxy R -> forall x : A, Morphisms.ProperProxy R x` .*by exact @Corelib.Classes.Morphisms.reflexive_proper_proxy*
            - ✅ We deduce `forall x : nat, Morphisms.ProperProxy eq x`.
          - ❌ We deduce `Morphisms.respectful eq iff (eq (S n0 + 0)) (eq (S (n0 + 0)))`, that is `forall x y : nat, x = y -> S n0 + 0 = x <-> S (n0 + 0) = y`.

            <details><summary>not proved</summary>

            ```
            1 goal
              
              n, n0 : nat
              H : forall x y : nat, x = y -> x + 0 = x <-> y + 0 = y
              H0 : 0 + 0 = 0
              H1 : S n0 + 0 = S (n0 + 0)
              H2 : n0 + 0 = n0 <-> S (n0 + 0) = S n0
              H3 : S n0 + 0 = S (n0 + 0)
              H4 : Morphisms.ProperProxy eq (S n0)
              H5 : S n0 + 0 = S (n0 + 0)
              H6 :
                Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq iff))
                  eq
              ============================
              Morphisms.respectful eq iff (eq (S n0 + 0)) (eq (S (n0 + 0)))
            
            File "./cyp_ko_85.v", line 4, characters 0-168:
            Error: No applicable tactic.
            ```

            </details>
            - ✅ By lemma we have `S n0 + 0 = S (n0 + 0)`.
            - ❌ We deduce `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq iff)) (@eq nat)`, that is `forall x y : nat, x = y -> Morphisms.respectful eq iff (eq x) (eq y)`.

              <details><summary>not proved</summary>

              ```
              1 goal
                
                n, n0 : nat
                H : forall x y : nat, x = y -> x + 0 = x <-> y + 0 = y
                H0 : 0 + 0 = 0
                H1 : S n0 + 0 = S (n0 + 0)
                H2 : n0 + 0 = n0 <-> S (n0 + 0) = S n0
                H3 : S n0 + 0 = S (n0 + 0)
                H4 : Morphisms.ProperProxy eq (S n0)
                H5 : S n0 + 0 = S (n0 + 0)
                H6 : RelationClasses.PER eq
                H7 :
                  forall (A : Type) (R : Relation_Definitions.relation A),
                  RelationClasses.PER R ->
                  Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful R iff)) R
                ============================
                Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq iff)) eq
              
              File "./cyp_ko_84.v", line 4, characters 0-168:
              Error: No applicable tactic.
              ```

              </details>
              - ✅ We deduce `RelationClasses.PER (@eq nat)`.
                - ✅ Using eq_equiv we get `RelationClasses.Equivalence (@eq nat)` .*by exact @Stdlib.Arith.PeanoNat.Nat.eq_equiv*
                - ✅ Using Equivalence_PER we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R` .*by exact @Corelib.Classes.RelationClasses.Equivalence_PER*
              - ✅ Using PER_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful R iff)) R` .*by exact @Corelib.Classes.Morphisms.PER_morphism*
        - ✅ We deduce `forall x : Prop, Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (iff x)`.
          - ✅ We deduce `RelationClasses.PER iff`.
            - ✅ Using iff_equivalence we get `RelationClasses.Equivalence iff` .*by exact @Corelib.Classes.RelationClasses.iff_equivalence*
            - ✅ Using Equivalence_PER we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R` .*by exact @Corelib.Classes.RelationClasses.Equivalence_PER*
          - ✅ Using trans_sym_co_inv_impl_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> forall x : A, Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)` .*by exact @Corelib.Classes.Morphisms.trans_sym_co_inv_impl_morphism*
        - ✅ We deduce `Basics.flip Basics.impl (n0 + 0 = n0 <-> S n0 + 0 = S n0) (n0 + 0 = n0 <-> S (n0 + 0) = S n0)`.
    - ✅ We deduce `n0 + 0 = n0 <-> S n0 + 0 = S n0`.
- ✅ Using bi_induction we get `forall A : nat -> Prop, Morphisms.Proper (Morphisms.respectful eq iff) A -> A 0 -> (forall n0 : nat, A n0 <-> A (S n0)) -> forall n0 : nat, A n0` .*by exact @Stdlib.Arith.PeanoNat.Nat.bi_induction*
- ✅ We deduce `forall n0 : nat, n0 + 0 = n0`.
- ✅ In particular `n + 0 = n`.

