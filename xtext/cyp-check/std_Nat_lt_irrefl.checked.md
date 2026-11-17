<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# Nat.lt_irrefl

✅ Let `x : nat`. We prove `~ x < x`.

- ✅ In particular `(x ?= x) = Lt <-> x < x`.
  - ❌ Using compare_lt_iff we get `forall n m : nat, (n ?= m) = Lt <-> n < m` .*by exact @compare_lt_iff*

    <details><summary>not proved</summary>

    ```
    1 goal
      
      x, n, m : nat
      ============================
      (n ?= m) = Lt <-> n < m
    
    File "./cyp_ko_1.v", line 4, characters 0-106:
    Error: No applicable tactic.
    ```

    </details>
- ✅ Rewriting with `(x ?= x) = Eq` from right to left (eq_ind_r), we get `(x ?= x) <> Lt`.
  - ✅ We have proved `Eq = Lt -> False`.
    - ▫️ Assume `Eq = Lt` (H).
      - ✅ Going back to the definition of eq (match) in `Eq = Lt` (H), we prove `Lt = Lt -> False`: (H0).
        - ▫️ Assume `Eq = Lt` (H0).
          - ✅ Rewriting with `Eq = Lt` from left to right (eq_ind), we get `match Lt with | Eq => True | _ => False end` (H1).
            - ✅ By definition of True (I), we have `True` .*by eapply @I; eauto*
            - ✅ By H0 we have `Eq = Lt`.
          - ✅ By contradiction (False, False_ind), from `False` (H1) we can deduce `False`.
      - ✅ By definition of eq (eq_refl), we have `Lt = Lt` .*by eapply @eq_refl; eauto*
      - ✅ By H0 we have `Lt = Lt -> False`.
      - ✅ We deduce `False`.
  - ✅ In particular `(x ?= x) = Eq`.
    - ❌ Using compare_refl we get `forall x0 : nat, (x0 ?= x0) = Eq` .*by exact @compare_refl*

      <details><summary>not proved</summary>

      ```
      1 goal
        
        x : nat
        H : (x ?= x) = Lt <-> x < x
        H0 : Eq = Lt -> False
        x0 : nat
        ============================
        (x0 ?= x0) = Eq
      
      File "./cyp_ko_12.v", line 4, characters 0-102:
      Error: No applicable tactic.
      ```

      </details>
- ✅ We have proved `(x ?= x) = Lt <-> x < x -> Basics.flip Basics.impl (~ x < x) ((x ?= x) <> Lt)`.
  - ▫️ Assume `(x ?= x) = Lt <-> x < x` (lemma).
    - ✅ We deduce `x < x <-> (x ?= x) = Lt`.
      - ✅ By lemma we have `(x ?= x) = Lt <-> x < x`.
      - ✅ In particular `(x ?= x) = Lt <-> x < x -> x < x <-> (x ?= x) = Lt`.
        - ❌ Using iff_Symmetric we get `RelationClasses.Symmetric iff` .*by exact @iff_Symmetric*

          <details><summary>not proved</summary>

          ```
          1 goal
            
            x : nat
            H : (x ?= x) = Lt <-> x < x
            H0 : (x ?= x) <> Lt
            H1, H2 : (x ?= x) = Lt <-> x < x
            ============================
            RelationClasses.Symmetric iff
          
          File "./cyp_ko_16.v", line 4, characters 0-104:
          Error: No applicable tactic.
          ```

          </details>
        - ✅ In particular `RelationClasses.Symmetric iff -> forall x0 y : Prop, x0 <-> y -> y <-> x0`.
          - ❌ Using symmetry we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Symmetric R -> forall x0 y : A, R x0 y -> R y x0` .*by exact @symmetry*

            <details><summary>not proved</summary>

            ```
            1 goal
              
              x : nat
              H : (x ?= x) = Lt <-> x < x
              H0 : (x ?= x) <> Lt
              H1, H2 : (x ?= x) = Lt <-> x < x
              H3 : RelationClasses.Symmetric iff
              A : Type
              R : Relation_Definitions.relation A
              H4 : RelationClasses.Symmetric R
              x0, y : A
              H5 : R x0 y
              ============================
              R y x0
            
            File "./cyp_ko_17.v", line 4, characters 0-94:
            Error: No applicable tactic.
            ```

            </details>
        - ✅ We deduce `forall x0 y : Prop, x0 <-> y -> y <-> x0`.
    - ✅ In particular `x < x <-> (x ?= x) = Lt -> Basics.flip Basics.impl (~ x < x) ((x ?= x) <> Lt)`.
      - ✅ We deduce `RelationClasses.subrelation (Morphisms.respectful iff iff) (Morphisms.respectful iff (Basics.flip Basics.impl))`.
        - ❌ Using iff_flip_impl_subrelation we get `RelationClasses.subrelation iff (Basics.flip Basics.impl)` .*by exact @iff_flip_impl_subrelation*

          <details><summary>not proved</summary>

          ```
          1 goal
            
            x : nat
            H : (x ?= x) = Lt <-> x < x
            H0 : (x ?= x) <> Lt
            H1 : (x ?= x) = Lt <-> x < x
            H2 : x < x <-> (x ?= x) = Lt
            ============================
            RelationClasses.subrelation iff (Basics.flip Basics.impl)
          
          File "./cyp_ko_22.v", line 4, characters 0-128:
          Error: No applicable tactic.
          ```

          </details>
        - ✅ In particular `RelationClasses.subrelation iff (Basics.flip Basics.impl) -> RelationClasses.subrelation (Morphisms.respectful iff iff) (Morphisms.respectful iff (Basics.flip Basics.impl))`.
          - ✅ In particular `RelationClasses.subrelation iff iff`.
            - ❌ Using subrelation_refl we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.subrelation R R` .*by exact @subrelation_refl*

              <details><summary>not proved</summary>

              ```
              1 goal
                
                x : nat
                H : (x ?= x) = Lt <-> x < x
                H0 : (x ?= x) <> Lt
                H1 : (x ?= x) = Lt <-> x < x
                H2 : x < x <-> (x ?= x) = Lt
                H3 : RelationClasses.subrelation iff (Basics.flip Basics.impl)
                A : Type
                R : Relation_Definitions.relation A
                ============================
                RelationClasses.subrelation R R
              
              File "./cyp_ko_23.v", line 4, characters 0-110:
              Error: No applicable tactic.
              ```

              </details>
          - ✅ In particular `RelationClasses.subrelation iff iff -> forall RB RB' : Relation_Definitions.relation Prop, RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful iff RB) (Morphisms.respectful iff RB')`.
            - ❌ Using subrelation_respectful we get `forall (A B : Type) (RA' RA : Relation_Definitions.relation A), RelationClasses.subrelation RA' RA -> forall RB RB' : Relation_Definitions.relation B, RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful RA RB) (Morphisms.respectful RA' RB')` .*by exact @subrelation_respectful*

              <details><summary>not proved</summary>

              ```
              1 goal
                
                x : nat
                H : (x ?= x) = Lt <-> x < x
                H0 : (x ?= x) <> Lt
                H1 : (x ?= x) = Lt <-> x < x
                H2 : x < x <-> (x ?= x) = Lt
                H3 : RelationClasses.subrelation iff (Basics.flip Basics.impl)
                H4 : RelationClasses.subrelation iff iff
                A : Type
                B : Type
                RA', RA : Relation_Definitions.relation A
                H5 : RelationClasses.subrelation RA' RA
                RB, RB' : Relation_Definitions.relation B
                H6 : RelationClasses.subrelation RB RB'
                ============================
                RelationClasses.subrelation (Morphisms.respectful RA RB)
                  (Morphisms.respectful RA' RB')
              
              File "./cyp_ko_25.v", line 4, characters 0-122:
              Error: No applicable tactic.
              ```

              </details>
          - ✅ We deduce `forall RB RB' : Relation_Definitions.relation Prop, RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful iff RB) (Morphisms.respectful iff RB')`.
      - ✅ In particular `RelationClasses.subrelation (Morphisms.respectful iff iff) (Morphisms.respectful iff (Basics.flip Basics.impl)) -> Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) not`.
        - ❌ Using not_iff_morphism we get `Morphisms.Proper (Morphisms.respectful iff iff) not` .*by exact @not_iff_morphism*

          <details><summary>not proved</summary>

          ```
          1 goal
            
            x : nat
            H : (x ?= x) = Lt <-> x < x
            H0 : (x ?= x) <> Lt
            H1 : (x ?= x) = Lt <-> x < x
            H2 : x < x <-> (x ?= x) = Lt
            H3 :
              RelationClasses.subrelation (Morphisms.respectful iff iff)
                (Morphisms.respectful iff (Basics.flip Basics.impl))
            ============================
            Morphisms.Proper (Morphisms.respectful iff iff) not
          
          File "./cyp_ko_30.v", line 4, characters 0-110:
          Error: No applicable tactic.
          ```

          </details>
        - ✅ In particular `Morphisms.Proper (Morphisms.respectful iff iff) not -> forall R : Relation_Definitions.relation (Prop -> Prop), Init.Unconvertible (Relation_Definitions.relation (Prop -> Prop)) R (Morphisms.respectful iff iff) -> RelationClasses.subrelation (Morphisms.respectful iff iff) R -> Morphisms.Proper R not`.
          - ❌ Using subrelation_proper we get `forall (A : Type) (R' : Relation_Definitions.relation A) (m : A), Morphisms.Proper R' m -> forall R : Relation_Definitions.relation A, Init.Unconvertible (Relation_Definitions.relation A) R R' -> RelationClasses.subrelation R' R -> Morphisms.Proper R m` .*by exact @subrelation_proper*

            <details><summary>not proved</summary>

            ```
            1 goal
              
              x : nat
              H : (x ?= x) = Lt <-> x < x
              H0 : (x ?= x) <> Lt
              H1 : (x ?= x) = Lt <-> x < x
              H2 : x < x <-> (x ?= x) = Lt
              H3 :
                RelationClasses.subrelation (Morphisms.respectful iff iff)
                  (Morphisms.respectful iff (Basics.flip Basics.impl))
              H4 : Morphisms.Proper (Morphisms.respectful iff iff) not
              A : Type
              R' : Relation_Definitions.relation A
              m : A
              H5 : Morphisms.Proper R' m
              R : Relation_Definitions.relation A
              H6 : Init.Unconvertible (Relation_Definitions.relation A) R R'
              H7 : RelationClasses.subrelation R' R
              ============================
              Morphisms.Proper R m
            
            File "./cyp_ko_31.v", line 4, characters 0-114:
            Error: No applicable tactic.
            ```

            </details>
        - ✅ We deduce `forall R : Relation_Definitions.relation (Prop -> Prop), Init.Unconvertible (Relation_Definitions.relation (Prop -> Prop)) R (Morphisms.respectful iff iff) -> RelationClasses.subrelation (Morphisms.respectful iff iff) R -> Morphisms.Proper R not`.
      - ✅ We deduce `Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) not`.
    - ✅ We deduce `Basics.flip Basics.impl (~ x < x) ((x ?= x) <> Lt)`.
- ✅ We deduce `~ x < x`.

