<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# Nat.mul_1_r

✅ Let `n : nat`. We prove `n * 1 = n`.

- ❌ Using one_succ we get `1 = 1` .*by exact @one_succ*

  <details><summary>not proved</summary>

  ```
  1 goal
    
    n : nat
    ============================
    1 = 1
  
  File "./cyp_ko_1.v", line 4, characters 0-94:
  Error: No applicable tactic.
  ```

  </details>
- ✅ We deduce `n * 1 = n`.
  - ✅ In particular `n * 1 = n * 0 + n`.
    - ❌ Using mul_succ_r we get `forall n0 m : nat, n0 * S m = n0 * m + n0` .*by exact @mul_succ_r*

      <details><summary>not proved</summary>

      ```
      1 goal
        
        n : nat
        H : 1 = 1
        n0, m : nat
        ============================
        n0 * S m = n0 * m + n0
      
      File "./cyp_ko_2.v", line 4, characters 0-98:
      Error: No applicable tactic.
      ```

      </details>
  - ✅ We deduce `n * 0 + n = n`.
    - ✅ In particular `n * 0 = 0`.
      - ❌ Using mul_0_r we get `forall n0 : nat, n0 * 0 = 0` .*by exact @mul_0_r*

        <details><summary>not proved</summary>

        ```
        1 goal
          
          n : nat
          H : 1 = 1
          H0 : n * 1 = n * 0 + n
          n0 : nat
          ============================
          n0 * 0 = 0
        
        File "./cyp_ko_4.v", line 4, characters 0-92:
        Error: No applicable tactic.
        ```

        </details>
    - ✅ We deduce `0 + n = n`.
      - ✅ In particular `0 + n = n`.
        - ❌ Using add_0_l we get `forall n0 : nat, 0 + n0 = n0` .*by exact @add_0_l*

          <details><summary>not proved</summary>

          ```
          1 goal
            
            n : nat
            H : 1 = 1
            H0 : n * 1 = n * 0 + n
            H1 : n * 0 = 0
            n0 : nat
            ============================
            0 + n0 = n0
          
          File "./cyp_ko_6.v", line 4, characters 0-92:
          Error: No applicable tactic.
          ```

          </details>
      - ❌ In particular `n = n`.

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
            CYP-KO 2
            CYP-OK 3
            CYP-KO 4
            CYP-OK 5
            CYP-KO 6
            CYP-OK 7
            File "./cyp_check.v", line 30, characters 97-124:
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
            CYP-KO 2
            CYP-OK 3
            CYP-KO 4
            CYP-OK 5
            CYP-KO 6
            CYP-OK 7
            File "./cyp_check.v", line 30, characters 97-122:
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
      - ✅ We have proved `0 + n = n -> Basics.flip Basics.impl (0 + n = n) (n = n)`.
        - ▫️ Assume `0 + n = n` (lemma).
          - ✅ In particular `Morphisms.ProperProxy eq n`.
            - ❌ Using eq_proper_proxy we get `forall (A : Type) (x : A), Morphisms.ProperProxy eq x` .*by exact @eq_proper_proxy*

              <details><summary>not proved</summary>

              ```
              1 goal
                
                n : nat
                H : 1 = 1
                H0 : n * 1 = n * 0 + n
                H1 : n * 0 = 0
                H2 : 0 + n = n
                H3 : n = n
                H4 : 0 + n = n
                A : Type
                x : A
                ============================
                Morphisms.ProperProxy eq x
              
              File "./cyp_ko_16.v", line 4, characters 0-108:
              Error: No applicable tactic.
              ```

              </details>
          - ✅ In particular `n = n -> Basics.flip Basics.impl (0 + n = n) (n = n)`.
            - ✅ By lemma we have `0 + n = n`.
            - ❌ In particular `0 + n = n -> Morphisms.respectful eq (Basics.flip Basics.impl) (eq (0 + n)) (eq n)`.

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
                  CYP-KO 2
                  CYP-OK 3
                  CYP-KO 4
                  CYP-OK 5
                  CYP-KO 6
                  CYP-OK 7
                  CYP-KO 16
                  CYP-OK 17
                  CYP-OK 18
                  File "./cyp_check.v", line 42, characters 176-203:
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
                  CYP-KO 2
                  CYP-OK 3
                  CYP-KO 4
                  CYP-OK 5
                  CYP-KO 6
                  CYP-OK 7
                  CYP-KO 16
                  CYP-OK 17
                  CYP-OK 18
                  File "./cyp_check.v", line 42, characters 176-202:
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
            - ✅ We deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (eq (0 + n)) (eq n)`.
          - ✅ We deduce `Basics.flip Basics.impl (0 + n = n) (n = n)`.
    - ✅ We have proved `n * 0 = 0 -> Basics.flip Basics.impl (n * 0 + n = n) (0 + n = n)`.
      - ▫️ Assume `n * 0 = 0` (lemma).
        - ✅ In particular `Morphisms.ProperProxy eq n`.
          - ❌ Using eq_proper_proxy we get `forall (A : Type) (x : A), Morphisms.ProperProxy eq x` .*by exact @eq_proper_proxy*

            <details><summary>not proved</summary>

            ```
            1 goal
              
              n : nat
              H : 1 = 1
              H0 : n * 1 = n * 0 + n
              H1 : n * 0 = 0
              H2 : 0 + n = n
              H3 : n * 0 = 0
              A : Type
              x : A
              ============================
              Morphisms.ProperProxy eq x
            
            File "./cyp_ko_32.v", line 4, characters 0-108:
            Error: No applicable tactic.
            ```

            </details>
        - ✅ In particular `n = n -> Basics.flip Basics.impl (n * 0 + n = n) (0 + n = n)`.
          - ✅ We deduce `n * 0 + n = 0 + n`.
            - ❌ In particular `Morphisms.ProperProxy eq n`.

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
                    CYP-KO 2
                    CYP-OK 3
                    CYP-KO 4
                    CYP-OK 5
                    CYP-KO 6
                    CYP-OK 7
                    CYP-KO 16
                    CYP-OK 17
                    CYP-OK 18
                    CYP-OK 27
                    CYP-OK 28
                    CYP-OK 29
                    CYP-OK 30
                    CYP-OK 31
                    CYP-KO 32
                    CYP-OK 33
                    File "./cyp_check.v", line 70, characters 146-173:
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
                    CYP-KO 2
                    CYP-OK 3
                    CYP-KO 4
                    CYP-OK 5
                    CYP-KO 6
                    CYP-OK 7
                    CYP-KO 16
                    CYP-OK 17
                    CYP-OK 18
                    CYP-OK 27
                    CYP-OK 28
                    CYP-OK 29
                    CYP-OK 30
                    CYP-OK 31
                    CYP-KO 32
                    CYP-OK 33
                    File "./cyp_check.v", line 70, characters 146-171:
                    Error: Cannot infer the implicit parameter A of RelationClasses.Reflexive
                    whose type is "Type" in environment:
                    n : nat
                    
                    
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
                  CYP-KO 2
                  CYP-OK 3
                  CYP-KO 4
                  CYP-OK 5
                  CYP-KO 6
                  CYP-OK 7
                  CYP-KO 16
                  CYP-OK 17
                  CYP-OK 18
                  CYP-OK 27
                  CYP-OK 28
                  CYP-OK 29
                  CYP-OK 30
                  CYP-OK 31
                  CYP-KO 32
                  CYP-OK 33
                  File "./cyp_check.v", line 70, characters 146-170:
                  Error: Cannot infer the implicit parameter A of Morphisms.ReflexiveProxy
                  whose type is "Type" in environment:
                  n : nat
                  
                  
                  ```

                  </details>
              - ❌ We deduce `forall x : nat, Morphisms.ProperProxy eq x`.

                <details><summary>Rocq error</summary>

                ```
                This step does not type-check because an earlier step does not: see the first Rocq error above.
                ```

                </details>
            - ✅ In particular `n = n -> n * 0 + n = 0 + n`.
              - ✅ By lemma we have `n * 0 = 0`.
              - ✅ In particular `n * 0 = 0 -> Morphisms.respectful eq eq (Init.Nat.add (n * 0)) (Init.Nat.add 0)`.
                - ❌ Using add_wd we get `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Init.Nat.add` .*by exact @add_wd*

                  <details><summary>not proved</summary>

                  ```
                  1 goal
                    
                    n : nat
                    H : 1 = 1
                    H0 : n * 1 = n * 0 + n
                    H1 : n * 0 = 0
                    H2 : 0 + n = n
                    H3 : n * 0 = 0
                    H4, H5 : Morphisms.ProperProxy eq n
                    H6 : n * 0 = 0
                    ============================
                    Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq))
                      Init.Nat.add
                  
                  File "./cyp_ko_46.v", line 4, characters 0-90:
                  Error: No applicable tactic.
                  ```

                  </details>
              - ✅ We deduce `Morphisms.respectful eq eq (Init.Nat.add (n * 0)) (Init.Nat.add 0)`.
          - ❌ In particular `n * 0 + n = 0 + n -> Morphisms.respectful eq (Basics.flip Basics.impl) (eq (n * 0 + n)) (eq (0 + n))`.

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
                CYP-KO 2
                CYP-OK 3
                CYP-KO 4
                CYP-OK 5
                CYP-KO 6
                CYP-OK 7
                CYP-KO 16
                CYP-OK 17
                CYP-OK 18
                CYP-OK 27
                CYP-OK 28
                CYP-OK 29
                CYP-OK 30
                CYP-OK 31
                CYP-KO 32
                CYP-OK 33
                CYP-OK 45
                CYP-KO 46
                CYP-OK 47
                CYP-OK 48
                CYP-OK 49
                CYP-OK 50
                File "./cyp_check.v", line 94, characters 171-198:
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
                CYP-KO 2
                CYP-OK 3
                CYP-KO 4
                CYP-OK 5
                CYP-KO 6
                CYP-OK 7
                CYP-KO 16
                CYP-OK 17
                CYP-OK 18
                CYP-OK 27
                CYP-OK 28
                CYP-OK 29
                CYP-OK 30
                CYP-OK 31
                CYP-KO 32
                CYP-OK 33
                CYP-OK 45
                CYP-KO 46
                CYP-OK 47
                CYP-OK 48
                CYP-OK 49
                CYP-OK 50
                File "./cyp_check.v", line 94, characters 171-197:
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
          - ✅ We deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (eq (n * 0 + n)) (eq (0 + n))`.
        - ✅ We deduce `Basics.flip Basics.impl (n * 0 + n = n) (0 + n = n)`.
  - ✅ We have proved `n * 1 = n * 0 + n -> Basics.flip Basics.impl (n * 1 = n) (n * 0 + n = n)`.
    - ▫️ Assume `n * 1 = n * 0 + n` (lemma).
      - ✅ In particular `Morphisms.ProperProxy eq n`.
        - ❌ Using eq_proper_proxy we get `forall (A : Type) (x : A), Morphisms.ProperProxy eq x` .*by exact @eq_proper_proxy*

          <details><summary>not proved</summary>

          ```
          1 goal
            
            n : nat
            H : 1 = 1
            H0 : n * 1 = n * 0 + n
            H1 : n * 0 + n = n
            H2 : n * 1 = n * 0 + n
            A : Type
            x : A
            ============================
            Morphisms.ProperProxy eq x
          
          File "./cyp_ko_64.v", line 4, characters 0-108:
          Error: No applicable tactic.
          ```

          </details>
      - ✅ In particular `n = n -> Basics.flip Basics.impl (n * 1 = n) (n * 0 + n = n)`.
        - ✅ By lemma we have `n * 1 = n * 0 + n`.
        - ❌ In particular `n * 1 = n * 0 + n -> Morphisms.respectful eq (Basics.flip Basics.impl) (eq (n * 1)) (eq (n * 0 + n))`.

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
              CYP-KO 2
              CYP-OK 3
              CYP-KO 4
              CYP-OK 5
              CYP-KO 6
              CYP-OK 7
              CYP-KO 16
              CYP-OK 17
              CYP-OK 18
              CYP-OK 27
              CYP-OK 28
              CYP-OK 29
              CYP-OK 30
              CYP-OK 31
              CYP-KO 32
              CYP-OK 33
              CYP-OK 45
              CYP-KO 46
              CYP-OK 47
              CYP-OK 48
              CYP-OK 49
              CYP-OK 50
              CYP-OK 59
              CYP-OK 60
              CYP-OK 61
              CYP-OK 62
              CYP-OK 63
              CYP-KO 64
              CYP-OK 65
              CYP-OK 66
              File "./cyp_check.v", line 126, characters 166-193:
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
              CYP-KO 2
              CYP-OK 3
              CYP-KO 4
              CYP-OK 5
              CYP-KO 6
              CYP-OK 7
              CYP-KO 16
              CYP-OK 17
              CYP-OK 18
              CYP-OK 27
              CYP-OK 28
              CYP-OK 29
              CYP-OK 30
              CYP-OK 31
              CYP-KO 32
              CYP-OK 33
              CYP-OK 45
              CYP-KO 46
              CYP-OK 47
              CYP-OK 48
              CYP-OK 49
              CYP-OK 50
              CYP-OK 59
              CYP-OK 60
              CYP-OK 61
              CYP-OK 62
              CYP-OK 63
              CYP-KO 64
              CYP-OK 65
              CYP-OK 66
              File "./cyp_check.v", line 126, characters 166-192:
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
        - ✅ We deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (eq (n * 1)) (eq (n * 0 + n))`.
      - ✅ We deduce `Basics.flip Basics.impl (n * 1 = n) (n * 0 + n = n)`.
- ✅ We have proved `1 = 1 -> Basics.flip Basics.impl (n * 1 = n) (n * 1 = n)`.
  - ▫️ Assume `1 = 1` (lemma).
    - ✅ In particular `Morphisms.ProperProxy eq n`.
      - ❌ Using eq_proper_proxy we get `forall (A : Type) (x : A), Morphisms.ProperProxy eq x` .*by exact @eq_proper_proxy*

        <details><summary>not proved</summary>

        ```
        1 goal
          
          n : nat
          H : 1 = 1
          H0 : n * 1 = n
          H1 : 1 = 1
          A : Type
          x : A
          ============================
          Morphisms.ProperProxy eq x
        
        File "./cyp_ko_80.v", line 4, characters 0-108:
        Error: No applicable tactic.
        ```

        </details>
    - ✅ In particular `n = n -> Basics.flip Basics.impl (n * 1 = n) (n * 1 = n)`.
      - ✅ We deduce `n * 1 = n * 1`.
        - ✅ By lemma we have `1 = 1`.
        - ✅ In particular `1 = 1 -> n * 1 = n * 1`.
          - ❌ In particular `Morphisms.ProperProxy eq n`.

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
                  CYP-KO 2
                  CYP-OK 3
                  CYP-KO 4
                  CYP-OK 5
                  CYP-KO 6
                  CYP-OK 7
                  CYP-KO 16
                  CYP-OK 17
                  CYP-OK 18
                  CYP-OK 27
                  CYP-OK 28
                  CYP-OK 29
                  CYP-OK 30
                  CYP-OK 31
                  CYP-KO 32
                  CYP-OK 33
                  CYP-OK 45
                  CYP-KO 46
                  CYP-OK 47
                  CYP-OK 48
                  CYP-OK 49
                  CYP-OK 50
                  CYP-OK 59
                  CYP-OK 60
                  CYP-OK 61
                  CYP-OK 62
                  CYP-OK 63
                  CYP-KO 64
                  CYP-OK 65
                  CYP-OK 66
                  CYP-OK 75
                  CYP-OK 76
                  CYP-OK 77
                  CYP-OK 78
                  CYP-OK 79
                  CYP-KO 80
                  CYP-OK 81
                  CYP-OK 82
                  File "./cyp_check.v", line 158, characters 113-140:
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
                  CYP-KO 2
                  CYP-OK 3
                  CYP-KO 4
                  CYP-OK 5
                  CYP-KO 6
                  CYP-OK 7
                  CYP-KO 16
                  CYP-OK 17
                  CYP-OK 18
                  CYP-OK 27
                  CYP-OK 28
                  CYP-OK 29
                  CYP-OK 30
                  CYP-OK 31
                  CYP-KO 32
                  CYP-OK 33
                  CYP-OK 45
                  CYP-KO 46
                  CYP-OK 47
                  CYP-OK 48
                  CYP-OK 49
                  CYP-OK 50
                  CYP-OK 59
                  CYP-OK 60
                  CYP-OK 61
                  CYP-OK 62
                  CYP-OK 63
                  CYP-KO 64
                  CYP-OK 65
                  CYP-OK 66
                  CYP-OK 75
                  CYP-OK 76
                  CYP-OK 77
                  CYP-OK 78
                  CYP-OK 79
                  CYP-KO 80
                  CYP-OK 81
                  CYP-OK 82
                  File "./cyp_check.v", line 158, characters 113-138:
                  Error: Cannot infer the implicit parameter A of RelationClasses.Reflexive
                  whose type is "Type" in environment:
                  n : nat
                  
                  
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
                CYP-KO 2
                CYP-OK 3
                CYP-KO 4
                CYP-OK 5
                CYP-KO 6
                CYP-OK 7
                CYP-KO 16
                CYP-OK 17
                CYP-OK 18
                CYP-OK 27
                CYP-OK 28
                CYP-OK 29
                CYP-OK 30
                CYP-OK 31
                CYP-KO 32
                CYP-OK 33
                CYP-OK 45
                CYP-KO 46
                CYP-OK 47
                CYP-OK 48
                CYP-OK 49
                CYP-OK 50
                CYP-OK 59
                CYP-OK 60
                CYP-OK 61
                CYP-OK 62
                CYP-OK 63
                CYP-KO 64
                CYP-OK 65
                CYP-OK 66
                CYP-OK 75
                CYP-OK 76
                CYP-OK 77
                CYP-OK 78
                CYP-OK 79
                CYP-KO 80
                CYP-OK 81
                CYP-OK 82
                File "./cyp_check.v", line 158, characters 113-137:
                Error: Cannot infer the implicit parameter A of Morphisms.ReflexiveProxy
                whose type is "Type" in environment:
                n : nat
                
                
                ```

                </details>
            - ❌ We deduce `forall x : nat, Morphisms.ProperProxy eq x`.

              <details><summary>Rocq error</summary>

              ```
              This step does not type-check because an earlier step does not: see the first Rocq error above.
              ```

              </details>
          - ✅ In particular `Morphisms.ProperProxy eq n -> Morphisms.Proper (Morphisms.respectful eq eq) (Nat.mul n)`.
            - ❌ Using mul_wd we get `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Init.Nat.mul` .*by exact @mul_wd*

              <details><summary>not proved</summary>

              ```
              1 goal
                
                n : nat
                H : 1 = 1
                H0 : n * 1 = n
                H1 : 1 = 1
                H2 : Morphisms.ProperProxy eq n
                H3 : 1 = 1
                H4 : Morphisms.ProperProxy eq n
                ============================
                Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq))
                  Init.Nat.mul
              
              File "./cyp_ko_94.v", line 4, characters 0-90:
              Error: No applicable tactic.
              ```

              </details>
            - ✅ In particular `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Nat.mul -> forall x : nat, Morphisms.ProperProxy eq x -> Morphisms.Proper (Morphisms.respectful eq eq) (Nat.mul x)`.
              - ❌ Using Reflexive_partial_app_morphism we get `forall (A B : Type) (R : Relation_Definitions.relation A) (R' : Relation_Definitions.relation B) (m : A -> B), Morphisms.Proper (Morphisms.respectful R R') m -> forall x : A, Morphisms.ProperProxy R x -> Morphisms.Proper R' (m x)` .*by exact @Reflexive_partial_app_morphism*

                <details><summary>not proved</summary>

                ```
                1 goal
                  
                  n : nat
                  H : 1 = 1
                  H0 : n * 1 = n
                  H1 : 1 = 1
                  H2 : Morphisms.ProperProxy eq n
                  H3 : 1 = 1
                  H4 : Morphisms.ProperProxy eq n
                  H5 :
                    Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq))
                      Init.Nat.mul
                  A : Type
                  B : Type
                  R : Relation_Definitions.relation A
                  R' : Relation_Definitions.relation B
                  m : A -> B
                  H6 : Morphisms.Proper (Morphisms.respectful R R') m
                  x : A
                  H7 : Morphisms.ProperProxy R x
                  ============================
                  Morphisms.Proper R' (m x)
                
                File "./cyp_ko_95.v", line 4, characters 0-138:
                Error: No applicable tactic.
                ```

                </details>
            - ✅ We deduce `forall x : nat, Morphisms.ProperProxy eq x -> Morphisms.Proper (Morphisms.respectful eq eq) (Nat.mul x)`.
          - ✅ We deduce `Morphisms.Proper (Morphisms.respectful eq eq) (Nat.mul n)`.
      - ❌ In particular `n * 1 = n * 1 -> Morphisms.respectful eq (Basics.flip Basics.impl) (eq (n * 1)) (eq (n * 1))`.

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
            CYP-KO 2
            CYP-OK 3
            CYP-KO 4
            CYP-OK 5
            CYP-KO 6
            CYP-OK 7
            CYP-KO 16
            CYP-OK 17
            CYP-OK 18
            CYP-OK 27
            CYP-OK 28
            CYP-OK 29
            CYP-OK 30
            CYP-OK 31
            CYP-KO 32
            CYP-OK 33
            CYP-OK 45
            CYP-KO 46
            CYP-OK 47
            CYP-OK 48
            CYP-OK 49
            CYP-OK 50
            CYP-OK 59
            CYP-OK 60
            CYP-OK 61
            CYP-OK 62
            CYP-OK 63
            CYP-KO 64
            CYP-OK 65
            CYP-OK 66
            CYP-OK 75
            CYP-OK 76
            CYP-OK 77
            CYP-OK 78
            CYP-OK 79
            CYP-KO 80
            CYP-OK 81
            CYP-OK 82
            CYP-KO 94
            CYP-KO 95
            CYP-OK 96
            CYP-OK 97
            CYP-OK 98
            CYP-OK 99
            CYP-OK 100
            CYP-OK 101
            File "./cyp_check.v", line 190, characters 121-148:
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
            CYP-KO 2
            CYP-OK 3
            CYP-KO 4
            CYP-OK 5
            CYP-KO 6
            CYP-OK 7
            CYP-KO 16
            CYP-OK 17
            CYP-OK 18
            CYP-OK 27
            CYP-OK 28
            CYP-OK 29
            CYP-OK 30
            CYP-OK 31
            CYP-KO 32
            CYP-OK 33
            CYP-OK 45
            CYP-KO 46
            CYP-OK 47
            CYP-OK 48
            CYP-OK 49
            CYP-OK 50
            CYP-OK 59
            CYP-OK 60
            CYP-OK 61
            CYP-OK 62
            CYP-OK 63
            CYP-KO 64
            CYP-OK 65
            CYP-OK 66
            CYP-OK 75
            CYP-OK 76
            CYP-OK 77
            CYP-OK 78
            CYP-OK 79
            CYP-KO 80
            CYP-OK 81
            CYP-OK 82
            CYP-KO 94
            CYP-KO 95
            CYP-OK 96
            CYP-OK 97
            CYP-OK 98
            CYP-OK 99
            CYP-OK 100
            CYP-OK 101
            File "./cyp_check.v", line 190, characters 121-147:
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
      - ✅ We deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (eq (n * 1)) (eq (n * 1))`.
    - ✅ We deduce `Basics.flip Basics.impl (n * 1 = n) (n * 1 = n)`.
- ✅ We deduce `n * 1 = n`.

