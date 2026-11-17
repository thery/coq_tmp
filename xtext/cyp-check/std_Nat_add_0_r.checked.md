<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# Nat.add_0_r

✅ Let `n : nat`. We prove `n + 0 = n`.

- ✅ Thus we have `forall x y : nat, x = y -> x + 0 = x <-> y + 0 = y`.
  - ▫️ Let us choose arbitrarily `x : nat`, `y : nat`.
    - ▫️ Assume `x = y` (H).
      - ✅ In particular `Morphisms.ProperProxy eq (y + 0 = y)`.
        - ❌ Using eq_proper_proxy we get `forall (A : Type) (x0 : A), Morphisms.ProperProxy eq x0` .*by exact @eq_proper_proxy*

          <details><summary>not proved</summary>

          ```
          1 goal
            
            n, x, y : nat
            H : x = y
            A : Type
            x0 : A
            ============================
            Morphisms.ProperProxy eq x0
          
          File "./cyp_ko_1.v", line 4, characters 0-108:
          Error: No applicable tactic.
          ```

          </details>
      - ✅ In particular `y + 0 = y <-> y + 0 = y`.
        - ❌ Using iff_Reflexive we get `RelationClasses.Reflexive iff` .*by exact @iff_Reflexive*

          <details><summary>not proved</summary>

          ```
          1 goal
            
            n, x, y : nat
            H : x = y
            H0 : Morphisms.ProperProxy eq (y + 0 = y)
            ============================
            RelationClasses.Reflexive iff
          
          File "./cyp_ko_3.v", line 4, characters 0-104:
          Error: No applicable tactic.
          ```

          </details>
        - ✅ In particular `RelationClasses.Reflexive iff -> forall x0 : Prop, x0 <-> x0`.
          - ❌ Using reflexivity we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x0 : A, R x0 x0` .*by exact @reflexivity*

            <details><summary>not proved</summary>

            ```
            1 goal
              
              n, x, y : nat
              H : x = y
              H0 : Morphisms.ProperProxy eq (y + 0 = y)
              H1 : RelationClasses.Reflexive iff
              A : Type
              R : Relation_Definitions.relation A
              H2 : RelationClasses.Reflexive R
              x0 : A
              ============================
              R x0 x0
            
            File "./cyp_ko_4.v", line 4, characters 0-100:
            Error: No applicable tactic.
            ```

            </details>
        - ✅ We deduce `forall x0 : Prop, x0 <-> x0`.
      - ✅ In particular `(y + 0 = y) = (y + 0 = y) -> Basics.flip Basics.impl (x + 0 = x <-> y + 0 = y) (y + 0 = y <-> y + 0 = y)`.
        - ✅ We deduce `x + 0 = x <-> y + 0 = y`.
          - ✅ By H we have `x = y`.
          - ✅ In particular `x = y -> x + 0 = x <-> y + 0 = y`.
            - ✅ We deduce `x + 0 = y + 0`.
              - ❌ In particular `Morphisms.ProperProxy eq 0`.

                <details><summary>Rocq error</summary>

                ```
                This step does not type-check because an earlier step does not: see the first Rocq error above.
                ```

                </details>
                - ❌ We deduce `Morphisms.ReflexiveProxy eq`.

                  <details><summary>Rocq error</summary>

                  ```
                  This step does not type-check because an earlier step does not: see the first Rocq error above.
                  ```

                  </details>
                  - ❌ We deduce `RelationClasses.Reflexive eq`.

                    <details><summary>Rocq error</summary>

                    ```
                    This step does not type-check because an earlier step does not: see the first Rocq error above.
                    ```

                    </details>
                    - ❌ Using eq_equiv we get `RelationClasses.Equivalence eq` .*by exact @eq_equiv*

                      <details><summary>Rocq error</summary>

                      ```
                      CYP-KO 1
                      CYP-OK 2
                      CYP-KO 3
                      CYP-KO 4
                      CYP-OK 5
                      CYP-OK 6
                      CYP-OK 7
                      CYP-OK 8
                      File "./cyp_check.v", line 34, characters 144-171:
                      Error: Cannot infer the implicit parameter A of RelationClasses.Equivalence
                      whose type is "Type" in environment:
                      n, x, y : nat
                      
                      
                      ```

                      </details>
                    - ❌ In particular `RelationClasses.Equivalence eq -> RelationClasses.Reflexive eq`.

                      <details><summary>Rocq error</summary>

                      ```
                      This step does not type-check because an earlier step does not: see the first Rocq error above.
                      ```

                      </details>
                      - ❌ Using Equivalence_Reflexive we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R` .*by exact @Equivalence_Reflexive*

                        <details><summary>Rocq error</summary>

                        ```
                        This step does not type-check because an earlier step does not: see the first Rocq error above.
                        ```

                        </details>
                  - ❌ In particular `RelationClasses.Reflexive eq -> Morphisms.ReflexiveProxy eq`.

                    <details><summary>Rocq error</summary>

                    ```
                    This step does not type-check because an earlier step does not: see the first Rocq error above.
                    ```

                    </details>
                    - ❌ Using reflexive_reflexive_proxy we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> Morphisms.ReflexiveProxy R` .*by exact @reflexive_reflexive_proxy*

                      <details><summary>Rocq error</summary>

                      ```
                      CYP-KO 1
                      CYP-OK 2
                      CYP-KO 3
                      CYP-KO 4
                      CYP-OK 5
                      CYP-OK 6
                      CYP-OK 7
                      CYP-OK 8
                      File "./cyp_check.v", line 34, characters 144-169:
                      Error: Cannot infer the implicit parameter A of RelationClasses.Reflexive
                      whose type is "Type" in environment:
                      n, x, y : nat
                      
                      
                      ```

                      </details>
                - ❌ In particular `Morphisms.ReflexiveProxy eq -> forall x0 : nat, Morphisms.ProperProxy eq x0`.

                  <details><summary>Rocq error</summary>

                  ```
                  This step does not type-check because an earlier step does not: see the first Rocq error above.
                  ```

                  </details>
                  - ❌ Using reflexive_proper_proxy we get `forall (A : Type) (R : Relation_Definitions.relation A), Morphisms.ReflexiveProxy R -> forall x0 : A, Morphisms.ProperProxy R x0` .*by exact @reflexive_proper_proxy*

                    <details><summary>Rocq error</summary>

                    ```
                    CYP-KO 1
                    CYP-OK 2
                    CYP-KO 3
                    CYP-KO 4
                    CYP-OK 5
                    CYP-OK 6
                    CYP-OK 7
                    CYP-OK 8
                    File "./cyp_check.v", line 34, characters 144-168:
                    Error: Cannot infer the implicit parameter A of Morphisms.ReflexiveProxy
                    whose type is "Type" in environment:
                    n, x, y : nat
                    
                    
                    ```

                    </details>
                - ❌ We deduce `forall x0 : nat, Morphisms.ProperProxy eq x0`.

                  <details><summary>Rocq error</summary>

                  ```
                  This step does not type-check because an earlier step does not: see the first Rocq error above.
                  ```

                  </details>
              - ✅ In particular `0 = 0 -> x + 0 = y + 0`.
                - ✅ By H we have `x = y`.
                - ✅ In particular `x = y -> Morphisms.respectful eq eq (Init.Nat.add x) (Init.Nat.add y)`.
                  - ❌ Using add_wd we get `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Init.Nat.add` .*by exact @add_wd*

                    <details><summary>not proved</summary>

                    ```
                    1 goal
                      
                      n, x, y : nat
                      H : x = y
                      H0 : Morphisms.ProperProxy eq (y + 0 = y)
                      H1 : y + 0 = y <-> y + 0 = y
                      H2 : x = y
                      H3 : Morphisms.ProperProxy eq 0
                      H4 : x = y
                      ============================
                      Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq))
                        Init.Nat.add
                    
                    File "./cyp_ko_21.v", line 4, characters 0-90:
                    Error: No applicable tactic.
                    ```

                    </details>
                - ✅ We deduce `Morphisms.respectful eq eq (Init.Nat.add x) (Init.Nat.add y)`.
            - ❌ In particular `x + 0 = y + 0 -> Morphisms.respectful eq iff (eq (x + 0)) (eq (y + 0))`.

              <details><summary>Rocq error</summary>

              ```
              This step does not type-check because an earlier step does not: see the first Rocq error above.
              ```

              </details>
              - ❌ We deduce `RelationClasses.PER eq`.

                <details><summary>Rocq error</summary>

                ```
                This step does not type-check because an earlier step does not: see the first Rocq error above.
                ```

                </details>
                - ❌ Using eq_equiv we get `RelationClasses.Equivalence eq` .*by exact @eq_equiv*

                  <details><summary>Rocq error</summary>

                  ```
                  CYP-KO 1
                  CYP-OK 2
                  CYP-KO 3
                  CYP-KO 4
                  CYP-OK 5
                  CYP-OK 6
                  CYP-OK 7
                  CYP-OK 8
                  CYP-OK 20
                  CYP-KO 21
                  CYP-OK 22
                  CYP-OK 23
                  CYP-OK 24
                  CYP-OK 25
                  File "./cyp_check.v", line 58, characters 165-192:
                  Error: Cannot infer the implicit parameter A of RelationClasses.Equivalence
                  whose type is "Type" in environment:
                  n, x, y : nat
                  
                  
                  ```

                  </details>
                - ❌ In particular `RelationClasses.Equivalence eq -> RelationClasses.PER eq`.

                  <details><summary>Rocq error</summary>

                  ```
                  This step does not type-check because an earlier step does not: see the first Rocq error above.
                  ```

                  </details>
                  - ❌ Using Equivalence_PER we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R` .*by exact @Equivalence_PER*

                    <details><summary>Rocq error</summary>

                    ```
                    This step does not type-check because an earlier step does not: see the first Rocq error above.
                    ```

                    </details>
              - ❌ In particular `RelationClasses.PER eq -> Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq iff)) eq`.

                <details><summary>Rocq error</summary>

                ```
                This step does not type-check because an earlier step does not: see the first Rocq error above.
                ```

                </details>
                - ❌ Using PER_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful R iff)) R` .*by exact @PER_morphism*

                  <details><summary>Rocq error</summary>

                  ```
                  CYP-KO 1
                  CYP-OK 2
                  CYP-KO 3
                  CYP-KO 4
                  CYP-OK 5
                  CYP-OK 6
                  CYP-OK 7
                  CYP-OK 8
                  CYP-OK 20
                  CYP-KO 21
                  CYP-OK 22
                  CYP-OK 23
                  CYP-OK 24
                  CYP-OK 25
                  File "./cyp_check.v", line 58, characters 165-184:
                  Error: Cannot infer the implicit parameter A of RelationClasses.PER whose
                  type is "Type" in environment:
                  n, x, y : nat
                  
                  
                  ```

                  </details>
              - ❌ We deduce `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq iff)) eq`.

                <details><summary>Rocq error</summary>

                ```
                This step does not type-check because an earlier step does not: see the first Rocq error above.
                ```

                </details>
            - ✅ We deduce `Morphisms.respectful eq iff (eq (x + 0)) (eq (y + 0))`.
        - ✅ In particular `x + 0 = x <-> y + 0 = y -> Morphisms.respectful eq (Basics.flip Basics.impl) (iff (x + 0 = x)) (iff (y + 0 = y))`.
          - ❌ Using iff_Transitive we get `RelationClasses.Transitive iff` .*by exact @iff_Transitive*

            <details><summary>not proved</summary>

            ```
            1 goal
              
              n, x, y : nat
              H : x = y
              H0 : Morphisms.ProperProxy eq (y + 0 = y)
              H1 : y + 0 = y <-> y + 0 = y
              H2 : x + 0 = x <-> y + 0 = y
              ============================
              RelationClasses.Transitive iff
            
            File "./cyp_ko_37.v", line 4, characters 0-106:
            Error: No applicable tactic.
            ```

            </details>
          - ✅ In particular `RelationClasses.Transitive iff -> Morphisms.Proper (Morphisms.respectful iff (Morphisms.respectful eq (Basics.flip Basics.impl))) iff`.
            - ❌ Using trans_co_eq_inv_impl_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Transitive R -> Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful eq (Basics.flip Basics.impl))) R` .*by exact @trans_co_eq_inv_impl_morphism*

              <details><summary>not proved</summary>

              ```
              1 goal
                
                n, x, y : nat
                H : x = y
                H0 : Morphisms.ProperProxy eq (y + 0 = y)
                H1 : y + 0 = y <-> y + 0 = y
                H2 : x + 0 = x <-> y + 0 = y
                H3 : RelationClasses.Transitive iff
                A : Type
                R : Relation_Definitions.relation A
                H4 : RelationClasses.Transitive R
                ============================
                Morphisms.Proper
                  (Morphisms.respectful R
                     (Morphisms.respectful eq (Basics.flip Basics.impl)))
                  R
              
              File "./cyp_ko_38.v", line 4, characters 0-136:
              Error: No applicable tactic.
              ```

              </details>
          - ✅ We deduce `Morphisms.Proper (Morphisms.respectful iff (Morphisms.respectful eq (Basics.flip Basics.impl))) iff`.
        - ✅ We deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (iff (x + 0 = x)) (iff (y + 0 = y))`.
      - ✅ We deduce `x + 0 = x <-> y + 0 = y`.
    - ✅ We have proved `x = y -> x + 0 = x <-> y + 0 = y`.
- ✅ We deduce `0 + 0 = 0`.
  - ✅ In particular `0 + 0 = 0`.
    - ❌ Using add_0_l we get `forall n0 : nat, 0 + n0 = n0` .*by exact @add_0_l*

      <details><summary>not proved</summary>

      ```
      1 goal
        
        n : nat
        H : forall x y : nat, x = y -> x + 0 = x <-> y + 0 = y
        n0 : nat
        ============================
        0 + n0 = n0
      
      File "./cyp_ko_47.v", line 4, characters 0-92:
      Error: No applicable tactic.
      ```

      </details>
  - ❌ In particular `0 = 0`.

    <details><summary>Rocq error</summary>

    ```
    This step does not type-check because an earlier step does not: see the first Rocq error above.
    ```

    </details>
    - ❌ We deduce `RelationClasses.Reflexive eq`.

      <details><summary>Rocq error</summary>

      ```
      This step does not type-check because an earlier step does not: see the first Rocq error above.
      ```

      </details>
      - ❌ Using eq_equiv we get `RelationClasses.Equivalence eq` .*by exact @eq_equiv*

        <details><summary>Rocq error</summary>

        ```
        CYP-KO 1
        CYP-OK 2
        CYP-KO 3
        CYP-KO 4
        CYP-OK 5
        CYP-OK 6
        CYP-OK 7
        CYP-OK 8
        CYP-OK 20
        CYP-KO 21
        CYP-OK 22
        CYP-OK 23
        CYP-OK 24
        CYP-OK 25
        CYP-OK 34
        CYP-OK 35
        CYP-OK 36
        CYP-KO 37
        CYP-KO 38
        CYP-OK 39
        CYP-OK 40
        CYP-OK 41
        CYP-OK 42
        CYP-OK 43
        CYP-OK 44
        CYP-OK 45
        CYP-OK 46
        CYP-KO 47
        CYP-OK 48
        File "./cyp_check.v", line 118, characters 100-127:
        Error: Cannot infer the implicit parameter A of RelationClasses.Equivalence
        whose type is "Type" in environment:
        n : nat
        
        
        ```

        </details>
      - ❌ In particular `RelationClasses.Equivalence eq -> RelationClasses.Reflexive eq`.

        <details><summary>Rocq error</summary>

        ```
        This step does not type-check because an earlier step does not: see the first Rocq error above.
        ```

        </details>
        - ❌ Using Equivalence_Reflexive we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R` .*by exact @Equivalence_Reflexive*

          <details><summary>Rocq error</summary>

          ```
          This step does not type-check because an earlier step does not: see the first Rocq error above.
          ```

          </details>
    - ❌ In particular `RelationClasses.Reflexive eq -> forall x : nat, x = x`.

      <details><summary>Rocq error</summary>

      ```
      This step does not type-check because an earlier step does not: see the first Rocq error above.
      ```

      </details>
      - ❌ Using reflexivity we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x : A, R x x` .*by exact @reflexivity*

        <details><summary>Rocq error</summary>

        ```
        CYP-KO 1
        CYP-OK 2
        CYP-KO 3
        CYP-KO 4
        CYP-OK 5
        CYP-OK 6
        CYP-OK 7
        CYP-OK 8
        CYP-OK 20
        CYP-KO 21
        CYP-OK 22
        CYP-OK 23
        CYP-OK 24
        CYP-OK 25
        CYP-OK 34
        CYP-OK 35
        CYP-OK 36
        CYP-KO 37
        CYP-KO 38
        CYP-OK 39
        CYP-OK 40
        CYP-OK 41
        CYP-OK 42
        CYP-OK 43
        CYP-OK 44
        CYP-OK 45
        CYP-OK 46
        CYP-KO 47
        CYP-OK 48
        File "./cyp_check.v", line 118, characters 100-125:
        Error: Cannot infer the implicit parameter A of RelationClasses.Reflexive
        whose type is "Type" in environment:
        n : nat
        
        
        ```

        </details>
    - ❌ We deduce `forall x : nat, x = x`.

      <details><summary>Rocq error</summary>

      ```
      This step does not type-check because an earlier step does not: see the first Rocq error above.
      ```

      </details>
  - ✅ We have proved `0 + 0 = 0 -> Basics.flip Basics.impl (0 + 0 = 0) (0 = 0)`.
    - ▫️ Assume `0 + 0 = 0` (lemma).
      - ✅ In particular `Morphisms.ProperProxy eq 0`.
        - ❌ Using eq_proper_proxy we get `forall (A : Type) (x : A), Morphisms.ProperProxy eq x` .*by exact @eq_proper_proxy*

          <details><summary>not proved</summary>

          ```
          1 goal
            
            n : nat
            H : forall x y : nat, x = y -> x + 0 = x <-> y + 0 = y
            H0 : 0 + 0 = 0
            H1 : 0 = 0
            H2 : 0 + 0 = 0
            A : Type
            x : A
            ============================
            Morphisms.ProperProxy eq x
          
          File "./cyp_ko_57.v", line 4, characters 0-108:
          Error: No applicable tactic.
          ```

          </details>
      - ✅ In particular `0 = 0 -> Basics.flip Basics.impl (0 + 0 = 0) (0 = 0)`.
        - ✅ By lemma we have `0 + 0 = 0`.
        - ❌ In particular `0 + 0 = 0 -> Morphisms.respectful eq (Basics.flip Basics.impl) (eq (0 + 0)) (eq 0)`.

          <details><summary>Rocq error</summary>

          ```
          This step does not type-check because an earlier step does not: see the first Rocq error above.
          ```

          </details>
          - ❌ We deduce `RelationClasses.Transitive eq`.

            <details><summary>Rocq error</summary>

            ```
            This step does not type-check because an earlier step does not: see the first Rocq error above.
            ```

            </details>
            - ❌ Using eq_equiv we get `RelationClasses.Equivalence eq` .*by exact @eq_equiv*

              <details><summary>Rocq error</summary>

              ```
              CYP-KO 1
              CYP-OK 2
              CYP-KO 3
              CYP-KO 4
              CYP-OK 5
              CYP-OK 6
              CYP-OK 7
              CYP-OK 8
              CYP-OK 20
              CYP-KO 21
              CYP-OK 22
              CYP-OK 23
              CYP-OK 24
              CYP-OK 25
              CYP-OK 34
              CYP-OK 35
              CYP-OK 36
              CYP-KO 37
              CYP-KO 38
              CYP-OK 39
              CYP-OK 40
              CYP-OK 41
              CYP-OK 42
              CYP-OK 43
              CYP-OK 44
              CYP-OK 45
              CYP-OK 46
              CYP-KO 47
              CYP-OK 48
              CYP-KO 57
              CYP-OK 58
              CYP-OK 59
              File "./cyp_check.v", line 130, characters 179-206:
              Error: Cannot infer the implicit parameter A of RelationClasses.Equivalence
              whose type is "Type" in environment:
              n : nat
              
              
              ```

              </details>
            - ❌ In particular `RelationClasses.Equivalence eq -> RelationClasses.Transitive eq`.

              <details><summary>Rocq error</summary>

              ```
              This step does not type-check because an earlier step does not: see the first Rocq error above.
              ```

              </details>
              - ❌ Using Equivalence_Transitive we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Transitive R` .*by exact @Equivalence_Transitive*

                <details><summary>Rocq error</summary>

                ```
                This step does not type-check because an earlier step does not: see the first Rocq error above.
                ```

                </details>
          - ❌ In particular `RelationClasses.Transitive eq -> Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq (Basics.flip Basics.impl))) eq`.

            <details><summary>Rocq error</summary>

            ```
            This step does not type-check because an earlier step does not: see the first Rocq error above.
            ```

            </details>
            - ❌ Using trans_co_eq_inv_impl_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Transitive R -> Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful eq (Basics.flip Basics.impl))) R` .*by exact @trans_co_eq_inv_impl_morphism*

              <details><summary>Rocq error</summary>

              ```
              CYP-KO 1
              CYP-OK 2
              CYP-KO 3
              CYP-KO 4
              CYP-OK 5
              CYP-OK 6
              CYP-OK 7
              CYP-OK 8
              CYP-OK 20
              CYP-KO 21
              CYP-OK 22
              CYP-OK 23
              CYP-OK 24
              CYP-OK 25
              CYP-OK 34
              CYP-OK 35
              CYP-OK 36
              CYP-KO 37
              CYP-KO 38
              CYP-OK 39
              CYP-OK 40
              CYP-OK 41
              CYP-OK 42
              CYP-OK 43
              CYP-OK 44
              CYP-OK 45
              CYP-OK 46
              CYP-KO 47
              CYP-OK 48
              CYP-KO 57
              CYP-OK 58
              CYP-OK 59
              File "./cyp_check.v", line 130, characters 179-205:
              Error: Cannot infer the implicit parameter A of RelationClasses.Transitive
              whose type is "Type" in environment:
              n : nat
              
              
              ```

              </details>
          - ❌ We deduce `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq (Basics.flip Basics.impl))) eq`.

            <details><summary>Rocq error</summary>

            ```
            This step does not type-check because an earlier step does not: see the first Rocq error above.
            ```

            </details>
        - ✅ We deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (eq (0 + 0)) (eq 0)`.
      - ✅ We deduce `Basics.flip Basics.impl (0 + 0 = 0) (0 = 0)`.
- ✅ We have `forall n0 : nat, n0 + 0 = n0 <-> S n0 + 0 = S n0`, since `n0` is arbitrary.
  - ▫️ Let us consider an arbitrary `n0 : nat`.
    - ✅ In particular `S n0 + 0 = S (n0 + 0)`.
      - ❌ Using add_succ_l we get `forall n1 m : nat, S n1 + m = S (n1 + m)` .*by exact @add_succ_l*

        <details><summary>not proved</summary>

        ```
        1 goal
          
          n, n0 : nat
          H : forall x y : nat, x = y -> x + 0 = x <-> y + 0 = y
          H0 : 0 + 0 = 0
          n1, m : nat
          ============================
          S n1 + m = S (n1 + m)
        
        File "./cyp_ko_73.v", line 4, characters 0-98:
        Error: No applicable tactic.
        ```

        </details>
    - ✅ We deduce `n0 + 0 = n0 <-> S (n0 + 0) = S n0`.
      - ✅ In particular `S (n0 + 0) = S n0 <-> n0 + 0 = n0`.
        - ❌ Using succ_inj_wd we get `forall n1 n2 : nat, S n1 = S n2 <-> n1 = n2` .*by exact @succ_inj_wd*

          <details><summary>not proved</summary>

          ```
          1 goal
            
            n, n0 : nat
            H : forall x y : nat, x = y -> x + 0 = x <-> y + 0 = y
            H0 : 0 + 0 = 0
            H1 : S n0 + 0 = S (n0 + 0)
            n1, n2 : nat
            ============================
            S n1 = S n2 <-> n1 = n2
          
          File "./cyp_ko_75.v", line 4, characters 0-100:
          Error: No applicable tactic.
          ```

          </details>
      - ✅ In particular `n0 + 0 = n0 <-> n0 + 0 = n0`.
        - ❌ Using iff_Reflexive we get `RelationClasses.Reflexive iff` .*by exact @iff_Reflexive*

          <details><summary>not proved</summary>

          ```
          1 goal
            
            n, n0 : nat
            H : forall x y : nat, x = y -> x + 0 = x <-> y + 0 = y
            H0 : 0 + 0 = 0
            H1 : S n0 + 0 = S (n0 + 0)
            H2 : S (n0 + 0) = S n0 <-> n0 + 0 = n0
            ============================
            RelationClasses.Reflexive iff
          
          File "./cyp_ko_77.v", line 4, characters 0-104:
          Error: No applicable tactic.
          ```

          </details>
        - ✅ In particular `RelationClasses.Reflexive iff -> forall x : Prop, x <-> x`.
          - ❌ Using reflexivity we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x : A, R x x` .*by exact @reflexivity*

            <details><summary>not proved</summary>

            ```
            1 goal
              
              n, n0 : nat
              H : forall x y : nat, x = y -> x + 0 = x <-> y + 0 = y
              H0 : 0 + 0 = 0
              H1 : S n0 + 0 = S (n0 + 0)
              H2 : S (n0 + 0) = S n0 <-> n0 + 0 = n0
              H3 : RelationClasses.Reflexive iff
              A : Type
              R : Relation_Definitions.relation A
              H4 : RelationClasses.Reflexive R
              x : A
              ============================
              R x x
            
            File "./cyp_ko_78.v", line 4, characters 0-100:
            Error: No applicable tactic.
            ```

            </details>
        - ✅ We deduce `forall x : Prop, x <-> x`.
      - ✅ We have proved `S (n0 + 0) = S n0 <-> n0 + 0 = n0 -> Basics.flip Basics.impl (n0 + 0 = n0 <-> S (n0 + 0) = S n0) (n0 + 0 = n0 <-> n0 + 0 = n0)`.
        - ▫️ Assume `S (n0 + 0) = S n0 <-> n0 + 0 = n0` (lemma).
          - ✅ By lemma we have `S (n0 + 0) = S n0 <-> n0 + 0 = n0`.
          - ✅ In particular `S (n0 + 0) = S n0 <-> n0 + 0 = n0 -> Basics.flip Basics.impl (n0 + 0 = n0 <-> S (n0 + 0) = S n0) (n0 + 0 = n0 <-> n0 + 0 = n0)`.
            - ✅ We deduce `RelationClasses.PER iff`.
              - ❌ Using iff_equivalence we get `RelationClasses.Equivalence iff` .*by exact @iff_equivalence*

                <details><summary>not proved</summary>

                ```
                1 goal
                  
                  n, n0 : nat
                  H : forall x y : nat, x = y -> x + 0 = x <-> y + 0 = y
                  H0 : 0 + 0 = 0
                  H1 : S n0 + 0 = S (n0 + 0)
                  H2 : S (n0 + 0) = S n0 <-> n0 + 0 = n0
                  H3 : n0 + 0 = n0 <-> n0 + 0 = n0
                  H4, H5 : S (n0 + 0) = S n0 <-> n0 + 0 = n0
                  ============================
                  RelationClasses.Equivalence iff
                
                File "./cyp_ko_83.v", line 4, characters 0-108:
                Error: No applicable tactic.
                ```

                </details>
              - ✅ In particular `RelationClasses.Equivalence iff -> RelationClasses.PER iff`.
                - ❌ Using Equivalence_PER we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R` .*by exact @Equivalence_PER*

                  <details><summary>not proved</summary>

                  ```
                  1 goal
                    
                    n, n0 : nat
                    H : forall x y : nat, x = y -> x + 0 = x <-> y + 0 = y
                    H0 : 0 + 0 = 0
                    H1 : S n0 + 0 = S (n0 + 0)
                    H2 : S (n0 + 0) = S n0 <-> n0 + 0 = n0
                    H3 : n0 + 0 = n0 <-> n0 + 0 = n0
                    H4, H5 : S (n0 + 0) = S n0 <-> n0 + 0 = n0
                    H6 : RelationClasses.Equivalence iff
                    A : Type
                    R : Relation_Definitions.relation A
                    H7 : RelationClasses.Equivalence R
                    ============================
                    RelationClasses.PER R
                  
                  File "./cyp_ko_84.v", line 4, characters 0-108:
                  Error: No applicable tactic.
                  ```

                  </details>
            - ✅ In particular `RelationClasses.PER iff -> forall x : Prop, Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (iff x)`.
              - ❌ Using trans_sym_co_inv_impl_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> forall x : A, Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)` .*by exact @trans_sym_co_inv_impl_morphism*

                <details><summary>not proved</summary>

                ```
                1 goal
                  
                  n, n0 : nat
                  H : forall x y : nat, x = y -> x + 0 = x <-> y + 0 = y
                  H0 : 0 + 0 = 0
                  H1 : S n0 + 0 = S (n0 + 0)
                  H2 : S (n0 + 0) = S n0 <-> n0 + 0 = n0
                  H3 : n0 + 0 = n0 <-> n0 + 0 = n0
                  H4, H5 : S (n0 + 0) = S n0 <-> n0 + 0 = n0
                  H6 : RelationClasses.PER iff
                  A : Type
                  R : Relation_Definitions.relation A
                  H7 : RelationClasses.PER R
                  x : A
                  ============================
                  Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)
                
                File "./cyp_ko_87.v", line 4, characters 0-138:
                Error: No applicable tactic.
                ```

                </details>
            - ✅ We deduce `forall x : Prop, Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (iff x)`.
          - ✅ We deduce `Basics.flip Basics.impl (n0 + 0 = n0 <-> S (n0 + 0) = S n0) (n0 + 0 = n0 <-> n0 + 0 = n0)`.
    - ✅ We have proved `S n0 + 0 = S (n0 + 0) -> Basics.flip Basics.impl (n0 + 0 = n0 <-> S n0 + 0 = S n0) (n0 + 0 = n0 <-> S (n0 + 0) = S n0)`.
      - ▫️ Assume `S n0 + 0 = S (n0 + 0)` (lemma).
        - ✅ We deduce `S n0 + 0 = S n0 <-> S (n0 + 0) = S n0`.
          - ❌ In particular `Morphisms.ProperProxy eq (S n0)`.

            <details><summary>Rocq error</summary>

            ```
            This step does not type-check because an earlier step does not: see the first Rocq error above.
            ```

            </details>
            - ❌ We deduce `Morphisms.ReflexiveProxy eq`.

              <details><summary>Rocq error</summary>

              ```
              This step does not type-check because an earlier step does not: see the first Rocq error above.
              ```

              </details>
              - ❌ We deduce `RelationClasses.Reflexive eq`.

                <details><summary>Rocq error</summary>

                ```
                This step does not type-check because an earlier step does not: see the first Rocq error above.
                ```

                </details>
                - ❌ Using eq_equiv we get `RelationClasses.Equivalence eq` .*by exact @eq_equiv*

                  <details><summary>Rocq error</summary>

                  ```
                  CYP-KO 1
                  CYP-OK 2
                  CYP-KO 3
                  CYP-KO 4
                  CYP-OK 5
                  CYP-OK 6
                  CYP-OK 7
                  CYP-OK 8
                  CYP-OK 20
                  CYP-KO 21
                  CYP-OK 22
                  CYP-OK 23
                  CYP-OK 24
                  CYP-OK 25
                  CYP-OK 34
                  CYP-OK 35
                  CYP-OK 36
                  CYP-KO 37
                  CYP-KO 38
                  CYP-OK 39
                  CYP-OK 40
                  CYP-OK 41
                  CYP-OK 42
                  CYP-OK 43
                  CYP-OK 44
                  CYP-OK 45
                  CYP-OK 46
                  CYP-KO 47
                  CYP-OK 48
                  CYP-KO 57
                  CYP-OK 58
                  CYP-OK 59
                  CYP-OK 68
                  CYP-OK 69
                  CYP-OK 70
                  CYP-OK 71
                  CYP-OK 72
                  CYP-KO 73
                  CYP-OK 74
                  CYP-KO 75
                  CYP-OK 76
                  CYP-KO 77
                  CYP-KO 78
                  CYP-OK 79
                  CYP-OK 80
                  CYP-OK 81
                  CYP-OK 82
                  CYP-KO 83
                  CYP-KO 84
                  CYP-OK 85
                  CYP-OK 86
                  CYP-KO 87
                  CYP-OK 88
                  CYP-OK 89
                  CYP-OK 90
                  CYP-OK 91
                  CYP-OK 92
                  CYP-OK 93
                  File "./cyp_check.v", line 234, characters 208-235:
                  Error: Cannot infer the implicit parameter A of RelationClasses.Equivalence
                  whose type is "Type" in environment:
                  n, n0 : nat
                  
                  
                  ```

                  </details>
                - ❌ In particular `RelationClasses.Equivalence eq -> RelationClasses.Reflexive eq`.

                  <details><summary>Rocq error</summary>

                  ```
                  This step does not type-check because an earlier step does not: see the first Rocq error above.
                  ```

                  </details>
                  - ❌ Using Equivalence_Reflexive we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R` .*by exact @Equivalence_Reflexive*

                    <details><summary>Rocq error</summary>

                    ```
                    This step does not type-check because an earlier step does not: see the first Rocq error above.
                    ```

                    </details>
              - ❌ In particular `RelationClasses.Reflexive eq -> Morphisms.ReflexiveProxy eq`.

                <details><summary>Rocq error</summary>

                ```
                This step does not type-check because an earlier step does not: see the first Rocq error above.
                ```

                </details>
                - ❌ Using reflexive_reflexive_proxy we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> Morphisms.ReflexiveProxy R` .*by exact @reflexive_reflexive_proxy*

                  <details><summary>Rocq error</summary>

                  ```
                  CYP-KO 1
                  CYP-OK 2
                  CYP-KO 3
                  CYP-KO 4
                  CYP-OK 5
                  CYP-OK 6
                  CYP-OK 7
                  CYP-OK 8
                  CYP-OK 20
                  CYP-KO 21
                  CYP-OK 22
                  CYP-OK 23
                  CYP-OK 24
                  CYP-OK 25
                  CYP-OK 34
                  CYP-OK 35
                  CYP-OK 36
                  CYP-KO 37
                  CYP-KO 38
                  CYP-OK 39
                  CYP-OK 40
                  CYP-OK 41
                  CYP-OK 42
                  CYP-OK 43
                  CYP-OK 44
                  CYP-OK 45
                  CYP-OK 46
                  CYP-KO 47
                  CYP-OK 48
                  CYP-KO 57
                  CYP-OK 58
                  CYP-OK 59
                  CYP-OK 68
                  CYP-OK 69
                  CYP-OK 70
                  CYP-OK 71
                  CYP-OK 72
                  CYP-KO 73
                  CYP-OK 74
                  CYP-KO 75
                  CYP-OK 76
                  CYP-KO 77
                  CYP-KO 78
                  CYP-OK 79
                  CYP-OK 80
                  CYP-OK 81
                  CYP-OK 82
                  CYP-KO 83
                  CYP-KO 84
                  CYP-OK 85
                  CYP-OK 86
                  CYP-KO 87
                  CYP-OK 88
                  CYP-OK 89
                  CYP-OK 90
                  CYP-OK 91
                  CYP-OK 92
                  CYP-OK 93
                  File "./cyp_check.v", line 234, characters 208-233:
                  Error: Cannot infer the implicit parameter A of RelationClasses.Reflexive
                  whose type is "Type" in environment:
                  n, n0 : nat
                  
                  
                  ```

                  </details>
            - ❌ In particular `Morphisms.ReflexiveProxy eq -> forall x : nat, Morphisms.ProperProxy eq x`.

              <details><summary>Rocq error</summary>

              ```
              This step does not type-check because an earlier step does not: see the first Rocq error above.
              ```

              </details>
              - ❌ Using reflexive_proper_proxy we get `forall (A : Type) (R : Relation_Definitions.relation A), Morphisms.ReflexiveProxy R -> forall x : A, Morphisms.ProperProxy R x` .*by exact @reflexive_proper_proxy*

                <details><summary>Rocq error</summary>

                ```
                CYP-KO 1
                CYP-OK 2
                CYP-KO 3
                CYP-KO 4
                CYP-OK 5
                CYP-OK 6
                CYP-OK 7
                CYP-OK 8
                CYP-OK 20
                CYP-KO 21
                CYP-OK 22
                CYP-OK 23
                CYP-OK 24
                CYP-OK 25
                CYP-OK 34
                CYP-OK 35
                CYP-OK 36
                CYP-KO 37
                CYP-KO 38
                CYP-OK 39
                CYP-OK 40
                CYP-OK 41
                CYP-OK 42
                CYP-OK 43
                CYP-OK 44
                CYP-OK 45
                CYP-OK 46
                CYP-KO 47
                CYP-OK 48
                CYP-KO 57
                CYP-OK 58
                CYP-OK 59
                CYP-OK 68
                CYP-OK 69
                CYP-OK 70
                CYP-OK 71
                CYP-OK 72
                CYP-KO 73
                CYP-OK 74
                CYP-KO 75
                CYP-OK 76
                CYP-KO 77
                CYP-KO 78
                CYP-OK 79
                CYP-OK 80
                CYP-OK 81
                CYP-OK 82
                CYP-KO 83
                CYP-KO 84
                CYP-OK 85
                CYP-OK 86
                CYP-KO 87
                CYP-OK 88
                CYP-OK 89
                CYP-OK 90
                CYP-OK 91
                CYP-OK 92
                CYP-OK 93
                File "./cyp_check.v", line 234, characters 208-232:
                Error: Cannot infer the implicit parameter A of Morphisms.ReflexiveProxy
                whose type is "Type" in environment:
                n, n0 : nat
                
                
                ```

                </details>
            - ❌ We deduce `forall x : nat, Morphisms.ProperProxy eq x`.

              <details><summary>Rocq error</summary>

              ```
              This step does not type-check because an earlier step does not: see the first Rocq error above.
              ```

              </details>
          - ✅ In particular `S n0 = S n0 -> S n0 + 0 = S n0 <-> S (n0 + 0) = S n0`.
            - ✅ By lemma we have `S n0 + 0 = S (n0 + 0)`.
            - ❌ In particular `S n0 + 0 = S (n0 + 0) -> Morphisms.respectful eq iff (eq (S n0 + 0)) (eq (S (n0 + 0)))`.

              <details><summary>Rocq error</summary>

              ```
              This step does not type-check because an earlier step does not: see the first Rocq error above.
              ```

              </details>
              - ❌ We deduce `RelationClasses.PER eq`.

                <details><summary>Rocq error</summary>

                ```
                This step does not type-check because an earlier step does not: see the first Rocq error above.
                ```

                </details>
                - ❌ Using eq_equiv we get `RelationClasses.Equivalence eq` .*by exact @eq_equiv*

                  <details><summary>Rocq error</summary>

                  ```
                  CYP-KO 1
                  CYP-OK 2
                  CYP-KO 3
                  CYP-KO 4
                  CYP-OK 5
                  CYP-OK 6
                  CYP-OK 7
                  CYP-OK 8
                  CYP-OK 20
                  CYP-KO 21
                  CYP-OK 22
                  CYP-OK 23
                  CYP-OK 24
                  CYP-OK 25
                  CYP-OK 34
                  CYP-OK 35
                  CYP-OK 36
                  CYP-KO 37
                  CYP-KO 38
                  CYP-OK 39
                  CYP-OK 40
                  CYP-OK 41
                  CYP-OK 42
                  CYP-OK 43
                  CYP-OK 44
                  CYP-OK 45
                  CYP-OK 46
                  CYP-KO 47
                  CYP-OK 48
                  CYP-KO 57
                  CYP-OK 58
                  CYP-OK 59
                  CYP-OK 68
                  CYP-OK 69
                  CYP-OK 70
                  CYP-OK 71
                  CYP-OK 72
                  CYP-KO 73
                  CYP-OK 74
                  CYP-KO 75
                  CYP-OK 76
                  CYP-KO 77
                  CYP-KO 78
                  CYP-OK 79
                  CYP-OK 80
                  CYP-OK 81
                  CYP-OK 82
                  CYP-KO 83
                  CYP-KO 84
                  CYP-OK 85
                  CYP-OK 86
                  CYP-KO 87
                  CYP-OK 88
                  CYP-OK 89
                  CYP-OK 90
                  CYP-OK 91
                  CYP-OK 92
                  CYP-OK 93
                  CYP-OK 105
                  File "./cyp_check.v", line 238, characters 276-303:
                  Error: Cannot infer the implicit parameter A of RelationClasses.Equivalence
                  whose type is "Type" in environment:
                  n, n0 : nat
                  
                  
                  ```

                  </details>
                - ❌ In particular `RelationClasses.Equivalence eq -> RelationClasses.PER eq`.

                  <details><summary>Rocq error</summary>

                  ```
                  This step does not type-check because an earlier step does not: see the first Rocq error above.
                  ```

                  </details>
                  - ❌ Using Equivalence_PER we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R` .*by exact @Equivalence_PER*

                    <details><summary>Rocq error</summary>

                    ```
                    This step does not type-check because an earlier step does not: see the first Rocq error above.
                    ```

                    </details>
              - ❌ In particular `RelationClasses.PER eq -> Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq iff)) eq`.

                <details><summary>Rocq error</summary>

                ```
                This step does not type-check because an earlier step does not: see the first Rocq error above.
                ```

                </details>
                - ❌ Using PER_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful R iff)) R` .*by exact @PER_morphism*

                  <details><summary>Rocq error</summary>

                  ```
                  CYP-KO 1
                  CYP-OK 2
                  CYP-KO 3
                  CYP-KO 4
                  CYP-OK 5
                  CYP-OK 6
                  CYP-OK 7
                  CYP-OK 8
                  CYP-OK 20
                  CYP-KO 21
                  CYP-OK 22
                  CYP-OK 23
                  CYP-OK 24
                  CYP-OK 25
                  CYP-OK 34
                  CYP-OK 35
                  CYP-OK 36
                  CYP-KO 37
                  CYP-KO 38
                  CYP-OK 39
                  CYP-OK 40
                  CYP-OK 41
                  CYP-OK 42
                  CYP-OK 43
                  CYP-OK 44
                  CYP-OK 45
                  CYP-OK 46
                  CYP-KO 47
                  CYP-OK 48
                  CYP-KO 57
                  CYP-OK 58
                  CYP-OK 59
                  CYP-OK 68
                  CYP-OK 69
                  CYP-OK 70
                  CYP-OK 71
                  CYP-OK 72
                  CYP-KO 73
                  CYP-OK 74
                  CYP-KO 75
                  CYP-OK 76
                  CYP-KO 77
                  CYP-KO 78
                  CYP-OK 79
                  CYP-OK 80
                  CYP-OK 81
                  CYP-OK 82
                  CYP-KO 83
                  CYP-KO 84
                  CYP-OK 85
                  CYP-OK 86
                  CYP-KO 87
                  CYP-OK 88
                  CYP-OK 89
                  CYP-OK 90
                  CYP-OK 91
                  CYP-OK 92
                  CYP-OK 93
                  CYP-OK 105
                  File "./cyp_check.v", line 238, characters 276-295:
                  Error: Cannot infer the implicit parameter A of RelationClasses.PER whose
                  type is "Type" in environment:
                  n, n0 : nat
                  
                  
                  ```

                  </details>
              - ❌ We deduce `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq iff)) eq`.

                <details><summary>Rocq error</summary>

                ```
                This step does not type-check because an earlier step does not: see the first Rocq error above.
                ```

                </details>
            - ✅ We deduce `Morphisms.respectful eq iff (eq (S n0 + 0)) (eq (S (n0 + 0)))`.
        - ✅ In particular `S n0 + 0 = S n0 <-> S (n0 + 0) = S n0 -> Basics.flip Basics.impl (n0 + 0 = n0 <-> S n0 + 0 = S n0) (n0 + 0 = n0 <-> S (n0 + 0) = S n0)`.
          - ✅ We deduce `RelationClasses.PER iff`.
            - ❌ Using iff_equivalence we get `RelationClasses.Equivalence iff` .*by exact @iff_equivalence*

              <details><summary>not proved</summary>

              ```
              1 goal
                
                n, n0 : nat
                H : forall x y : nat, x = y -> x + 0 = x <-> y + 0 = y
                H0 : 0 + 0 = 0
                H1 : S n0 + 0 = S (n0 + 0)
                H2 : n0 + 0 = n0 <-> S (n0 + 0) = S n0
                H3 : S n0 + 0 = S (n0 + 0)
                H4 : S n0 + 0 = S n0 <-> S (n0 + 0) = S n0
                ============================
                RelationClasses.Equivalence iff
              
              File "./cyp_ko_117.v", line 4, characters 0-108:
              Error: No applicable tactic.
              ```

              </details>
            - ✅ In particular `RelationClasses.Equivalence iff -> RelationClasses.PER iff`.
              - ❌ Using Equivalence_PER we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R` .*by exact @Equivalence_PER*

                <details><summary>not proved</summary>

                ```
                1 goal
                  
                  n, n0 : nat
                  H : forall x y : nat, x = y -> x + 0 = x <-> y + 0 = y
                  H0 : 0 + 0 = 0
                  H1 : S n0 + 0 = S (n0 + 0)
                  H2 : n0 + 0 = n0 <-> S (n0 + 0) = S n0
                  H3 : S n0 + 0 = S (n0 + 0)
                  H4 : S n0 + 0 = S n0 <-> S (n0 + 0) = S n0
                  H5 : RelationClasses.Equivalence iff
                  A : Type
                  R : Relation_Definitions.relation A
                  H6 : RelationClasses.Equivalence R
                  ============================
                  RelationClasses.PER R
                
                File "./cyp_ko_118.v", line 4, characters 0-108:
                Error: No applicable tactic.
                ```

                </details>
          - ✅ In particular `RelationClasses.PER iff -> forall x : Prop, Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (iff x)`.
            - ❌ Using trans_sym_co_inv_impl_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> forall x : A, Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)` .*by exact @trans_sym_co_inv_impl_morphism*

              <details><summary>not proved</summary>

              ```
              1 goal
                
                n, n0 : nat
                H : forall x y : nat, x = y -> x + 0 = x <-> y + 0 = y
                H0 : 0 + 0 = 0
                H1 : S n0 + 0 = S (n0 + 0)
                H2 : n0 + 0 = n0 <-> S (n0 + 0) = S n0
                H3 : S n0 + 0 = S (n0 + 0)
                H4 : S n0 + 0 = S n0 <-> S (n0 + 0) = S n0
                H5 : RelationClasses.PER iff
                A : Type
                R : Relation_Definitions.relation A
                H6 : RelationClasses.PER R
                x : A
                ============================
                Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)
              
              File "./cyp_ko_121.v", line 4, characters 0-138:
              Error: No applicable tactic.
              ```

              </details>
          - ✅ We deduce `forall x : Prop, Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (iff x)`.
        - ✅ We deduce `Basics.flip Basics.impl (n0 + 0 = n0 <-> S n0 + 0 = S n0) (n0 + 0 = n0 <-> S (n0 + 0) = S n0)`.
    - ✅ We deduce `n0 + 0 = n0 <-> S n0 + 0 = S n0`.
- ✅ In particular `Morphisms.Proper (Morphisms.respectful eq iff) (fun t : nat => t + 0 = t) -> 0 + 0 = 0 -> (forall n0 : nat, n0 + 0 = n0 <-> S n0 + 0 = S n0) -> forall n0 : nat, n0 + 0 = n0`.
  - ❌ Using bi_induction we get `forall A : nat -> Prop, Morphisms.Proper (Morphisms.respectful eq iff) A -> A 0 -> (forall n0 : nat, A n0 <-> A (S n0)) -> forall n0 : nat, A n0` .*by exact @bi_induction*

    <details><summary>not proved</summary>

    ```
    1 goal
      
      n : nat
      H : forall x y : nat, x = y -> x + 0 = x <-> y + 0 = y
      H0 : 0 + 0 = 0
      H1 : forall n0 : nat, n0 + 0 = n0 <-> S n0 + 0 = S n0
      A : nat -> Prop
      H2 : Morphisms.Proper (Morphisms.respectful eq iff) A
      H3 : A 0
      H4 : forall n0 : nat, A n0 <-> A (S n0)
      n0 : nat
      ============================
      A n0
    
    File "./cyp_ko_129.v", line 4, characters 0-102:
    Error: No applicable tactic.
    ```

    </details>
- ✅ We deduce `forall n0 : nat, n0 + 0 = n0`.
- ✅ In particular `n + 0 = n`.

