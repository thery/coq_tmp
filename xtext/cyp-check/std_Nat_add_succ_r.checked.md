<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# Nat.add_succ_r

✅ Let `n m : nat`. We prove `n + S m = S (n + m)`.

- ✅ Thus we have `forall x y : nat, x = y -> x + S m = S (x + m) <-> y + S m = S (y + m)`.
  - ▫️ Let us choose arbitrarily `x : nat`, `y : nat`.
    - ▫️ Assume `x = y` (H).
      - ✅ In particular `Morphisms.ProperProxy eq (y + S m = S (y + m))`.
        - ❌ Using eq_proper_proxy we get `forall (A : Type) (x0 : A), Morphisms.ProperProxy eq x0` .*by exact @eq_proper_proxy*

          <details><summary>not proved</summary>

          ```
          1 goal
            
            n, m, x, y : nat
            H : x = y
            A : Type
            x0 : A
            ============================
            Morphisms.ProperProxy eq x0
          
          File "./cyp_ko_1.v", line 4, characters 0-108:
          Error: No applicable tactic.
          ```

          </details>
      - ✅ In particular `y + S m = S (y + m) <-> y + S m = S (y + m)`.
        - ❌ Using iff_Reflexive we get `RelationClasses.Reflexive iff` .*by exact @iff_Reflexive*

          <details><summary>not proved</summary>

          ```
          1 goal
            
            n, m, x, y : nat
            H : x = y
            H0 : Morphisms.ProperProxy eq (y + S m = S (y + m))
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
              
              n, m, x, y : nat
              H : x = y
              H0 : Morphisms.ProperProxy eq (y + S m = S (y + m))
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
      - ✅ In particular `(y + S m = S (y + m)) = (y + S m = S (y + m)) -> Basics.flip Basics.impl (x + S m = S (x + m) <-> y + S m = S (y + m)) (y + S m = S (y + m) <-> y + S m = S (y + m))`.
        - ✅ We deduce `x + S m = S (x + m) <-> y + S m = S (y + m)`.
          - ✅ We deduce `S (x + m) = S (y + m)`.
            - ✅ We deduce `x + m = y + m`.
              - ❌ In particular `Morphisms.ProperProxy eq m`.

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
                      File "./cyp_check.v", line 30, characters 163-190:
                      Error: Cannot infer the implicit parameter A of RelationClasses.Equivalence
                      whose type is "Type" in environment:
                      n, m, x, y : nat
                      
                      
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
                      File "./cyp_check.v", line 30, characters 163-188:
                      Error: Cannot infer the implicit parameter A of RelationClasses.Reflexive
                      whose type is "Type" in environment:
                      n, m, x, y : nat
                      
                      
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
                    File "./cyp_check.v", line 30, characters 163-187:
                    Error: Cannot infer the implicit parameter A of Morphisms.ReflexiveProxy
                    whose type is "Type" in environment:
                    n, m, x, y : nat
                    
                    
                    ```

                    </details>
                - ❌ We deduce `forall x0 : nat, Morphisms.ProperProxy eq x0`.

                  <details><summary>Rocq error</summary>

                  ```
                  This step does not type-check because an earlier step does not: see the first Rocq error above.
                  ```

                  </details>
              - ✅ In particular `m = m -> x + m = y + m`.
                - ✅ By H we have `x = y`.
                - ✅ In particular `x = y -> Morphisms.respectful eq eq (Init.Nat.add x) (Init.Nat.add y)`.
                  - ❌ Using add_wd we get `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Init.Nat.add` .*by exact @add_wd*

                    <details><summary>not proved</summary>

                    ```
                    1 goal
                      
                      n, m, x, y : nat
                      H : x = y
                      H0 : Morphisms.ProperProxy eq (y + S m = S (y + m))
                      H1 : y + S m = S (y + m) <-> y + S m = S (y + m)
                      H2 : Morphisms.ProperProxy eq m
                      H3 : x = y
                      ============================
                      Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq))
                        Init.Nat.add
                    
                    File "./cyp_ko_20.v", line 4, characters 0-90:
                    Error: No applicable tactic.
                    ```

                    </details>
                - ✅ We deduce `Morphisms.respectful eq eq (Init.Nat.add x) (Init.Nat.add y)`.
            - ✅ In particular `x + m = y + m -> S (x + m) = S (y + m)`.
              - ❌ Using succ_wd we get `Morphisms.Proper (Morphisms.respectful eq eq) S` .*by exact @succ_wd*

                <details><summary>not proved</summary>

                ```
                1 goal
                  
                  n, m, x, y : nat
                  H : x = y
                  H0 : Morphisms.ProperProxy eq (y + S m = S (y + m))
                  H1 : y + S m = S (y + m) <-> y + S m = S (y + m)
                  H2 : x + m = y + m
                  ============================
                  Morphisms.Proper (Morphisms.respectful eq eq) S
                
                File "./cyp_ko_25.v", line 4, characters 0-92:
                Error: No applicable tactic.
                ```

                </details>
          - ✅ In particular `S (x + m) = S (y + m) -> x + S m = S (x + m) <-> y + S m = S (y + m)`.
            - ✅ We deduce `x + S m = y + S m`.
              - ❌ In particular `Morphisms.ProperProxy eq (S m)`.

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
                      CYP-OK 19
                      CYP-KO 20
                      CYP-OK 21
                      CYP-OK 22
                      CYP-OK 23
                      CYP-OK 24
                      CYP-KO 25
                      CYP-OK 26
                      CYP-OK 27
                      File "./cyp_check.v", line 66, characters 192-219:
                      Error: Cannot infer the implicit parameter A of RelationClasses.Equivalence
                      whose type is "Type" in environment:
                      n, m, x, y : nat
                      
                      
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
                      CYP-OK 19
                      CYP-KO 20
                      CYP-OK 21
                      CYP-OK 22
                      CYP-OK 23
                      CYP-OK 24
                      CYP-KO 25
                      CYP-OK 26
                      CYP-OK 27
                      File "./cyp_check.v", line 66, characters 192-217:
                      Error: Cannot infer the implicit parameter A of RelationClasses.Reflexive
                      whose type is "Type" in environment:
                      n, m, x, y : nat
                      
                      
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
                    CYP-OK 19
                    CYP-KO 20
                    CYP-OK 21
                    CYP-OK 22
                    CYP-OK 23
                    CYP-OK 24
                    CYP-KO 25
                    CYP-OK 26
                    CYP-OK 27
                    File "./cyp_check.v", line 66, characters 192-216:
                    Error: Cannot infer the implicit parameter A of Morphisms.ReflexiveProxy
                    whose type is "Type" in environment:
                    n, m, x, y : nat
                    
                    
                    ```

                    </details>
                - ❌ We deduce `forall x0 : nat, Morphisms.ProperProxy eq x0`.

                  <details><summary>Rocq error</summary>

                  ```
                  This step does not type-check because an earlier step does not: see the first Rocq error above.
                  ```

                  </details>
              - ✅ In particular `S m = S m -> x + S m = y + S m`.
                - ✅ By H we have `x = y`.
                - ✅ In particular `x = y -> Morphisms.respectful eq eq (Init.Nat.add x) (Init.Nat.add y)`.
                  - ❌ Using add_wd we get `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Init.Nat.add` .*by exact @add_wd*

                    <details><summary>not proved</summary>

                    ```
                    1 goal
                      
                      n, m, x, y : nat
                      H : x = y
                      H0 : Morphisms.ProperProxy eq (y + S m = S (y + m))
                      H1 : y + S m = S (y + m) <-> y + S m = S (y + m)
                      H2 : S (x + m) = S (y + m)
                      H3 : Morphisms.ProperProxy eq (S m)
                      H4 : x = y
                      ============================
                      Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq))
                        Init.Nat.add
                    
                    File "./cyp_ko_40.v", line 4, characters 0-90:
                    Error: No applicable tactic.
                    ```

                    </details>
                - ✅ We deduce `Morphisms.respectful eq eq (Init.Nat.add x) (Init.Nat.add y)`.
            - ❌ In particular `x + S m = y + S m -> Morphisms.respectful eq iff (eq (x + S m)) (eq (y + S m))`.

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
                  CYP-OK 19
                  CYP-KO 20
                  CYP-OK 21
                  CYP-OK 22
                  CYP-OK 23
                  CYP-OK 24
                  CYP-KO 25
                  CYP-OK 26
                  CYP-OK 27
                  CYP-OK 39
                  CYP-KO 40
                  CYP-OK 41
                  CYP-OK 42
                  CYP-OK 43
                  CYP-OK 44
                  File "./cyp_check.v", line 90, characters 217-244:
                  Error: Cannot infer the implicit parameter A of RelationClasses.Equivalence
                  whose type is "Type" in environment:
                  n, m, x, y : nat
                  
                  
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
                  CYP-OK 19
                  CYP-KO 20
                  CYP-OK 21
                  CYP-OK 22
                  CYP-OK 23
                  CYP-OK 24
                  CYP-KO 25
                  CYP-OK 26
                  CYP-OK 27
                  CYP-OK 39
                  CYP-KO 40
                  CYP-OK 41
                  CYP-OK 42
                  CYP-OK 43
                  CYP-OK 44
                  File "./cyp_check.v", line 90, characters 217-236:
                  Error: Cannot infer the implicit parameter A of RelationClasses.PER whose
                  type is "Type" in environment:
                  n, m, x, y : nat
                  
                  
                  ```

                  </details>
              - ❌ We deduce `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq iff)) eq`.

                <details><summary>Rocq error</summary>

                ```
                This step does not type-check because an earlier step does not: see the first Rocq error above.
                ```

                </details>
            - ✅ We deduce `Morphisms.respectful eq iff (eq (x + S m)) (eq (y + S m))`.
        - ✅ In particular `x + S m = S (x + m) <-> y + S m = S (y + m) -> Morphisms.respectful eq (Basics.flip Basics.impl) (iff (x + S m = S (x + m))) (iff (y + S m = S (y + m)))`.
          - ❌ Using iff_Transitive we get `RelationClasses.Transitive iff` .*by exact @iff_Transitive*

            <details><summary>not proved</summary>

            ```
            1 goal
              
              n, m, x, y : nat
              H : x = y
              H0 : Morphisms.ProperProxy eq (y + S m = S (y + m))
              H1 : y + S m = S (y + m) <-> y + S m = S (y + m)
              H2 : x + S m = S (x + m) <-> y + S m = S (y + m)
              ============================
              RelationClasses.Transitive iff
            
            File "./cyp_ko_56.v", line 4, characters 0-106:
            Error: No applicable tactic.
            ```

            </details>
          - ✅ In particular `RelationClasses.Transitive iff -> Morphisms.Proper (Morphisms.respectful iff (Morphisms.respectful eq (Basics.flip Basics.impl))) iff`.
            - ❌ Using trans_co_eq_inv_impl_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Transitive R -> Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful eq (Basics.flip Basics.impl))) R` .*by exact @trans_co_eq_inv_impl_morphism*

              <details><summary>not proved</summary>

              ```
              1 goal
                
                n, m, x, y : nat
                H : x = y
                H0 : Morphisms.ProperProxy eq (y + S m = S (y + m))
                H1 : y + S m = S (y + m) <-> y + S m = S (y + m)
                H2 : x + S m = S (x + m) <-> y + S m = S (y + m)
                H3 : RelationClasses.Transitive iff
                A : Type
                R : Relation_Definitions.relation A
                H4 : RelationClasses.Transitive R
                ============================
                Morphisms.Proper
                  (Morphisms.respectful R
                     (Morphisms.respectful eq (Basics.flip Basics.impl)))
                  R
              
              File "./cyp_ko_57.v", line 4, characters 0-136:
              Error: No applicable tactic.
              ```

              </details>
          - ✅ We deduce `Morphisms.Proper (Morphisms.respectful iff (Morphisms.respectful eq (Basics.flip Basics.impl))) iff`.
        - ✅ We deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (iff (x + S m = S (x + m))) (iff (y + S m = S (y + m)))`.
      - ✅ We deduce `x + S m = S (x + m) <-> y + S m = S (y + m)`.
    - ✅ We have proved `x = y -> x + S m = S (x + m) <-> y + S m = S (y + m)`.
- ✅ We deduce `0 + S m = S (0 + m)`.
  - ✅ In particular `0 + S m = S m`.
    - ❌ Using add_0_l we get `forall n0 : nat, 0 + n0 = n0` .*by exact @add_0_l*

      <details><summary>not proved</summary>

      ```
      1 goal
        
        n, m : nat
        H : forall x y : nat, x = y -> x + S m = S (x + m) <-> y + S m = S (y + m)
        n0 : nat
        ============================
        0 + n0 = n0
      
      File "./cyp_ko_66.v", line 4, characters 0-92:
      Error: No applicable tactic.
      ```

      </details>
  - ✅ We deduce `S m = S (0 + m)`.
    - ✅ In particular `0 + m = m`.
      - ❌ Using add_0_l we get `forall n0 : nat, 0 + n0 = n0` .*by exact @add_0_l*

        <details><summary>not proved</summary>

        ```
        1 goal
          
          n, m : nat
          H : forall x y : nat, x = y -> x + S m = S (x + m) <-> y + S m = S (y + m)
          H0 : 0 + S m = S m
          n0 : nat
          ============================
          0 + n0 = n0
        
        File "./cyp_ko_68.v", line 4, characters 0-92:
        Error: No applicable tactic.
        ```

        </details>
    - ❌ In particular `S m = S m`.

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
          CYP-OK 19
          CYP-KO 20
          CYP-OK 21
          CYP-OK 22
          CYP-OK 23
          CYP-OK 24
          CYP-KO 25
          CYP-OK 26
          CYP-OK 27
          CYP-OK 39
          CYP-KO 40
          CYP-OK 41
          CYP-OK 42
          CYP-OK 43
          CYP-OK 44
          CYP-OK 53
          CYP-OK 54
          CYP-OK 55
          CYP-KO 56
          CYP-KO 57
          CYP-OK 58
          CYP-OK 59
          CYP-OK 60
          CYP-OK 61
          CYP-OK 62
          CYP-OK 63
          CYP-OK 64
          CYP-OK 65
          CYP-KO 66
          CYP-OK 67
          CYP-KO 68
          CYP-OK 69
          File "./cyp_check.v", line 158, characters 143-170:
          Error: Cannot infer the implicit parameter A of RelationClasses.Equivalence
          whose type is "Type" in environment:
          n, m : nat
          
          
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
          CYP-OK 19
          CYP-KO 20
          CYP-OK 21
          CYP-OK 22
          CYP-OK 23
          CYP-OK 24
          CYP-KO 25
          CYP-OK 26
          CYP-OK 27
          CYP-OK 39
          CYP-KO 40
          CYP-OK 41
          CYP-OK 42
          CYP-OK 43
          CYP-OK 44
          CYP-OK 53
          CYP-OK 54
          CYP-OK 55
          CYP-KO 56
          CYP-KO 57
          CYP-OK 58
          CYP-OK 59
          CYP-OK 60
          CYP-OK 61
          CYP-OK 62
          CYP-OK 63
          CYP-OK 64
          CYP-OK 65
          CYP-KO 66
          CYP-OK 67
          CYP-KO 68
          CYP-OK 69
          File "./cyp_check.v", line 158, characters 143-168:
          Error: Cannot infer the implicit parameter A of RelationClasses.Reflexive
          whose type is "Type" in environment:
          n, m : nat
          
          
          ```

          </details>
      - ❌ We deduce `forall x : nat, x = x`.

        <details><summary>Rocq error</summary>

        ```
        This step does not type-check because an earlier step does not: see the first Rocq error above.
        ```

        </details>
    - ✅ We have proved `0 + m = m -> Basics.flip Basics.impl (S m = S (0 + m)) (S m = S m)`.
      - ▫️ Assume `0 + m = m` (lemma).
        - ✅ We deduce `S (0 + m) = S m`.
          - ✅ By lemma we have `0 + m = m`.
          - ✅ In particular `0 + m = m -> S (0 + m) = S m`.
            - ❌ Using succ_wd we get `Morphisms.Proper (Morphisms.respectful eq eq) S` .*by exact @succ_wd*

              <details><summary>not proved</summary>

              ```
              1 goal
                
                n, m : nat
                H : forall x y : nat, x = y -> x + S m = S (x + m) <-> y + S m = S (y + m)
                H0 : 0 + S m = S m
                H1 : 0 + m = m
                H2 : S m = S m
                H3, H4 : 0 + m = m
                ============================
                Morphisms.Proper (Morphisms.respectful eq eq) S
              
              File "./cyp_ko_79.v", line 4, characters 0-92:
              Error: No applicable tactic.
              ```

              </details>
        - ❌ In particular `S (0 + m) = S m -> Basics.flip Basics.impl (S m = S (0 + m)) (S m = S m)`.

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
              CYP-OK 19
              CYP-KO 20
              CYP-OK 21
              CYP-OK 22
              CYP-OK 23
              CYP-OK 24
              CYP-KO 25
              CYP-OK 26
              CYP-OK 27
              CYP-OK 39
              CYP-KO 40
              CYP-OK 41
              CYP-OK 42
              CYP-OK 43
              CYP-OK 44
              CYP-OK 53
              CYP-OK 54
              CYP-OK 55
              CYP-KO 56
              CYP-KO 57
              CYP-OK 58
              CYP-OK 59
              CYP-OK 60
              CYP-OK 61
              CYP-OK 62
              CYP-OK 63
              CYP-OK 64
              CYP-OK 65
              CYP-KO 66
              CYP-OK 67
              CYP-KO 68
              CYP-OK 69
              CYP-OK 78
              CYP-KO 79
              CYP-OK 80
              CYP-OK 81
              File "./cyp_check.v", line 174, characters 198-225:
              Error: Cannot infer the implicit parameter A of RelationClasses.Equivalence
              whose type is "Type" in environment:
              n, m : nat
              
              
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
          - ❌ In particular `RelationClasses.PER eq -> forall x : nat, Morphisms.Proper (Morphisms.respectful eq (Basics.flip Basics.impl)) (eq x)`.

            <details><summary>Rocq error</summary>

            ```
            This step does not type-check because an earlier step does not: see the first Rocq error above.
            ```

            </details>
            - ❌ Using trans_sym_co_inv_impl_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> forall x : A, Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)` .*by exact @trans_sym_co_inv_impl_morphism*

              <details><summary>Rocq error</summary>

              ```
              CYP-KO 1
              CYP-OK 2
              CYP-KO 3
              CYP-KO 4
              CYP-OK 5
              CYP-OK 6
              CYP-OK 7
              CYP-OK 19
              CYP-KO 20
              CYP-OK 21
              CYP-OK 22
              CYP-OK 23
              CYP-OK 24
              CYP-KO 25
              CYP-OK 26
              CYP-OK 27
              CYP-OK 39
              CYP-KO 40
              CYP-OK 41
              CYP-OK 42
              CYP-OK 43
              CYP-OK 44
              CYP-OK 53
              CYP-OK 54
              CYP-OK 55
              CYP-KO 56
              CYP-KO 57
              CYP-OK 58
              CYP-OK 59
              CYP-OK 60
              CYP-OK 61
              CYP-OK 62
              CYP-OK 63
              CYP-OK 64
              CYP-OK 65
              CYP-KO 66
              CYP-OK 67
              CYP-KO 68
              CYP-OK 69
              CYP-OK 78
              CYP-KO 79
              CYP-OK 80
              CYP-OK 81
              File "./cyp_check.v", line 174, characters 198-217:
              Error: Cannot infer the implicit parameter A of RelationClasses.PER whose
              type is "Type" in environment:
              n, m : nat
              
              
              ```

              </details>
          - ❌ We deduce `forall x : nat, Morphisms.Proper (Morphisms.respectful eq (Basics.flip Basics.impl)) (eq x)`.

            <details><summary>Rocq error</summary>

            ```
            This step does not type-check because an earlier step does not: see the first Rocq error above.
            ```

            </details>
        - ✅ We deduce `Basics.flip Basics.impl (S m = S (0 + m)) (S m = S m)`.
  - ✅ We have proved `0 + S m = S m -> Basics.flip Basics.impl (0 + S m = S (0 + m)) (S m = S (0 + m))`.
    - ▫️ Assume `0 + S m = S m` (lemma).
      - ✅ In particular `Morphisms.ProperProxy eq (S (0 + m))`.
        - ❌ Using eq_proper_proxy we get `forall (A : Type) (x : A), Morphisms.ProperProxy eq x` .*by exact @eq_proper_proxy*

          <details><summary>not proved</summary>

          ```
          1 goal
            
            n, m : nat
            H : forall x y : nat, x = y -> x + S m = S (x + m) <-> y + S m = S (y + m)
            H0 : 0 + S m = S m
            H1 : S m = S (0 + m)
            H2 : 0 + S m = S m
            A : Type
            x : A
            ============================
            Morphisms.ProperProxy eq x
          
          File "./cyp_ko_93.v", line 4, characters 0-108:
          Error: No applicable tactic.
          ```

          </details>
      - ✅ In particular `S (0 + m) = S (0 + m) -> Basics.flip Basics.impl (0 + S m = S (0 + m)) (S m = S (0 + m))`.
        - ✅ By lemma we have `0 + S m = S m`.
        - ❌ In particular `0 + S m = S m -> Morphisms.respectful eq (Basics.flip Basics.impl) (eq (0 + S m)) (eq (S m))`.

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
              CYP-OK 19
              CYP-KO 20
              CYP-OK 21
              CYP-OK 22
              CYP-OK 23
              CYP-OK 24
              CYP-KO 25
              CYP-OK 26
              CYP-OK 27
              CYP-OK 39
              CYP-KO 40
              CYP-OK 41
              CYP-OK 42
              CYP-OK 43
              CYP-OK 44
              CYP-OK 53
              CYP-OK 54
              CYP-OK 55
              CYP-KO 56
              CYP-KO 57
              CYP-OK 58
              CYP-OK 59
              CYP-OK 60
              CYP-OK 61
              CYP-OK 62
              CYP-OK 63
              CYP-OK 64
              CYP-OK 65
              CYP-KO 66
              CYP-OK 67
              CYP-KO 68
              CYP-OK 69
              CYP-OK 78
              CYP-KO 79
              CYP-OK 80
              CYP-OK 81
              CYP-OK 90
              CYP-OK 91
              CYP-OK 92
              CYP-KO 93
              CYP-OK 94
              CYP-OK 95
              File "./cyp_check.v", line 198, characters 233-260:
              Error: Cannot infer the implicit parameter A of RelationClasses.Equivalence
              whose type is "Type" in environment:
              n, m : nat
              
              
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
              CYP-OK 19
              CYP-KO 20
              CYP-OK 21
              CYP-OK 22
              CYP-OK 23
              CYP-OK 24
              CYP-KO 25
              CYP-OK 26
              CYP-OK 27
              CYP-OK 39
              CYP-KO 40
              CYP-OK 41
              CYP-OK 42
              CYP-OK 43
              CYP-OK 44
              CYP-OK 53
              CYP-OK 54
              CYP-OK 55
              CYP-KO 56
              CYP-KO 57
              CYP-OK 58
              CYP-OK 59
              CYP-OK 60
              CYP-OK 61
              CYP-OK 62
              CYP-OK 63
              CYP-OK 64
              CYP-OK 65
              CYP-KO 66
              CYP-OK 67
              CYP-KO 68
              CYP-OK 69
              CYP-OK 78
              CYP-KO 79
              CYP-OK 80
              CYP-OK 81
              CYP-OK 90
              CYP-OK 91
              CYP-OK 92
              CYP-KO 93
              CYP-OK 94
              CYP-OK 95
              File "./cyp_check.v", line 198, characters 233-259:
              Error: Cannot infer the implicit parameter A of RelationClasses.Transitive
              whose type is "Type" in environment:
              n, m : nat
              
              
              ```

              </details>
          - ❌ We deduce `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq (Basics.flip Basics.impl))) eq`.

            <details><summary>Rocq error</summary>

            ```
            This step does not type-check because an earlier step does not: see the first Rocq error above.
            ```

            </details>
        - ✅ We deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (eq (0 + S m)) (eq (S m))`.
      - ✅ We deduce `Basics.flip Basics.impl (0 + S m = S (0 + m)) (S m = S (0 + m))`.
- ✅ We have `forall n0 : nat, n0 + S m = S (n0 + m) <-> S n0 + S m = S (S n0 + m)`, since `n0` is arbitrary.
  - ▫️ Let us consider an arbitrary `n0 : nat`.
    - ✅ In particular `S n0 + S m = S (n0 + S m)`.
      - ❌ Using add_succ_l we get `forall n1 m0 : nat, S n1 + m0 = S (n1 + m0)` .*by exact @add_succ_l*

        <details><summary>not proved</summary>

        ```
        1 goal
          
          n, m, n0 : nat
          H : forall x y : nat, x = y -> x + S m = S (x + m) <-> y + S m = S (y + m)
          H0 : 0 + S m = S (0 + m)
          n1, m0 : nat
          ============================
          S n1 + m0 = S (n1 + m0)
        
        File "./cyp_ko_109.v", line 4, characters 0-98:
        Error: No applicable tactic.
        ```

        </details>
    - ✅ We deduce `n0 + S m = S (n0 + m) <-> S (n0 + S m) = S (S n0 + m)`.
      - ✅ In particular `S n0 + m = S (n0 + m)`.
        - ❌ Using add_succ_l we get `forall n1 m0 : nat, S n1 + m0 = S (n1 + m0)` .*by exact @add_succ_l*

          <details><summary>not proved</summary>

          ```
          1 goal
            
            n, m, n0 : nat
            H : forall x y : nat, x = y -> x + S m = S (x + m) <-> y + S m = S (y + m)
            H0 : 0 + S m = S (0 + m)
            H1 : S n0 + S m = S (n0 + S m)
            n1, m0 : nat
            ============================
            S n1 + m0 = S (n1 + m0)
          
          File "./cyp_ko_111.v", line 4, characters 0-98:
          Error: No applicable tactic.
          ```

          </details>
      - ✅ We deduce `n0 + S m = S (n0 + m) <-> S (n0 + S m) = S (S (n0 + m))`.
        - ✅ In particular `S (n0 + S m) = S (S (n0 + m)) <-> n0 + S m = S (n0 + m)`.
          - ❌ Using succ_inj_wd we get `forall n1 n2 : nat, S n1 = S n2 <-> n1 = n2` .*by exact @succ_inj_wd*

            <details><summary>not proved</summary>

            ```
            1 goal
              
              n, m, n0 : nat
              H : forall x y : nat, x = y -> x + S m = S (x + m) <-> y + S m = S (y + m)
              H0 : 0 + S m = S (0 + m)
              H1 : S n0 + S m = S (n0 + S m)
              H2 : S n0 + m = S (n0 + m)
              n1, n2 : nat
              ============================
              S n1 = S n2 <-> n1 = n2
            
            File "./cyp_ko_113.v", line 4, characters 0-100:
            Error: No applicable tactic.
            ```

            </details>
        - ✅ In particular `n0 + S m = S (n0 + m) <-> n0 + S m = S (n0 + m)`.
          - ❌ Using iff_Reflexive we get `RelationClasses.Reflexive iff` .*by exact @iff_Reflexive*

            <details><summary>not proved</summary>

            ```
            1 goal
              
              n, m, n0 : nat
              H : forall x y : nat, x = y -> x + S m = S (x + m) <-> y + S m = S (y + m)
              H0 : 0 + S m = S (0 + m)
              H1 : S n0 + S m = S (n0 + S m)
              H2 : S n0 + m = S (n0 + m)
              H3 : S (n0 + S m) = S (S (n0 + m)) <-> n0 + S m = S (n0 + m)
              ============================
              RelationClasses.Reflexive iff
            
            File "./cyp_ko_115.v", line 4, characters 0-104:
            Error: No applicable tactic.
            ```

            </details>
          - ✅ In particular `RelationClasses.Reflexive iff -> forall x : Prop, x <-> x`.
            - ❌ Using reflexivity we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x : A, R x x` .*by exact @reflexivity*

              <details><summary>not proved</summary>

              ```
              1 goal
                
                n, m, n0 : nat
                H : forall x y : nat, x = y -> x + S m = S (x + m) <-> y + S m = S (y + m)
                H0 : 0 + S m = S (0 + m)
                H1 : S n0 + S m = S (n0 + S m)
                H2 : S n0 + m = S (n0 + m)
                H3 : S (n0 + S m) = S (S (n0 + m)) <-> n0 + S m = S (n0 + m)
                H4 : RelationClasses.Reflexive iff
                A : Type
                R : Relation_Definitions.relation A
                H5 : RelationClasses.Reflexive R
                x : A
                ============================
                R x x
              
              File "./cyp_ko_116.v", line 4, characters 0-100:
              Error: No applicable tactic.
              ```

              </details>
          - ✅ We deduce `forall x : Prop, x <-> x`.
        - ✅ We have proved `S (n0 + S m) = S (S (n0 + m)) <-> n0 + S m = S (n0 + m) -> Basics.flip Basics.impl (n0 + S m = S (n0 + m) <-> S (n0 + S m) = S (S (n0 + m))) (n0 + S m = S (n0 + m) <-> n0 + S m = S (n0 + m))`.
          - ▫️ Assume `S (n0 + S m) = S (S (n0 + m)) <-> n0 + S m = S (n0 + m)` (lemma).
            - ✅ By lemma we have `S (n0 + S m) = S (S (n0 + m)) <-> n0 + S m = S (n0 + m)`.
            - ✅ In particular `S (n0 + S m) = S (S (n0 + m)) <-> n0 + S m = S (n0 + m) -> Basics.flip Basics.impl (n0 + S m = S (n0 + m) <-> S (n0 + S m) = S (S (n0 + m))) (n0 + S m = S (n0 + m) <-> n0 + S m = S (n0 + m))`.
              - ✅ We deduce `RelationClasses.PER iff`.
                - ❌ Using iff_equivalence we get `RelationClasses.Equivalence iff` .*by exact @iff_equivalence*

                  <details><summary>not proved</summary>

                  ```
                  1 goal
                    
                    n, m, n0 : nat
                    H : forall x y : nat, x = y -> x + S m = S (x + m) <-> y + S m = S (y + m)
                    H0 : 0 + S m = S (0 + m)
                    H1 : S n0 + S m = S (n0 + S m)
                    H2 : S n0 + m = S (n0 + m)
                    H3 : S (n0 + S m) = S (S (n0 + m)) <-> n0 + S m = S (n0 + m)
                    H4 : n0 + S m = S (n0 + m) <-> n0 + S m = S (n0 + m)
                    H5, H6 : S (n0 + S m) = S (S (n0 + m)) <-> n0 + S m = S (n0 + m)
                    ============================
                    RelationClasses.Equivalence iff
                  
                  File "./cyp_ko_121.v", line 4, characters 0-108:
                  Error: No applicable tactic.
                  ```

                  </details>
                - ✅ In particular `RelationClasses.Equivalence iff -> RelationClasses.PER iff`.
                  - ❌ Using Equivalence_PER we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R` .*by exact @Equivalence_PER*

                    <details><summary>not proved</summary>

                    ```
                    1 goal
                      
                      n, m, n0 : nat
                      H : forall x y : nat, x = y -> x + S m = S (x + m) <-> y + S m = S (y + m)
                      H0 : 0 + S m = S (0 + m)
                      H1 : S n0 + S m = S (n0 + S m)
                      H2 : S n0 + m = S (n0 + m)
                      H3 : S (n0 + S m) = S (S (n0 + m)) <-> n0 + S m = S (n0 + m)
                      H4 : n0 + S m = S (n0 + m) <-> n0 + S m = S (n0 + m)
                      H5, H6 : S (n0 + S m) = S (S (n0 + m)) <-> n0 + S m = S (n0 + m)
                      H7 : RelationClasses.Equivalence iff
                      A : Type
                      R : Relation_Definitions.relation A
                      H8 : RelationClasses.Equivalence R
                      ============================
                      RelationClasses.PER R
                    
                    File "./cyp_ko_122.v", line 4, characters 0-108:
                    Error: No applicable tactic.
                    ```

                    </details>
              - ✅ In particular `RelationClasses.PER iff -> forall x : Prop, Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (iff x)`.
                - ❌ Using trans_sym_co_inv_impl_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> forall x : A, Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)` .*by exact @trans_sym_co_inv_impl_morphism*

                  <details><summary>not proved</summary>

                  ```
                  1 goal
                    
                    n, m, n0 : nat
                    H : forall x y : nat, x = y -> x + S m = S (x + m) <-> y + S m = S (y + m)
                    H0 : 0 + S m = S (0 + m)
                    H1 : S n0 + S m = S (n0 + S m)
                    H2 : S n0 + m = S (n0 + m)
                    H3 : S (n0 + S m) = S (S (n0 + m)) <-> n0 + S m = S (n0 + m)
                    H4 : n0 + S m = S (n0 + m) <-> n0 + S m = S (n0 + m)
                    H5, H6 : S (n0 + S m) = S (S (n0 + m)) <-> n0 + S m = S (n0 + m)
                    H7 : RelationClasses.PER iff
                    A : Type
                    R : Relation_Definitions.relation A
                    H8 : RelationClasses.PER R
                    x : A
                    ============================
                    Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)
                  
                  File "./cyp_ko_125.v", line 4, characters 0-138:
                  Error: No applicable tactic.
                  ```

                  </details>
              - ✅ We deduce `forall x : Prop, Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (iff x)`.
            - ✅ We deduce `Basics.flip Basics.impl (n0 + S m = S (n0 + m) <-> S (n0 + S m) = S (S (n0 + m))) (n0 + S m = S (n0 + m) <-> n0 + S m = S (n0 + m))`.
      - ✅ We have proved `S n0 + m = S (n0 + m) -> Basics.flip Basics.impl (n0 + S m = S (n0 + m) <-> S (n0 + S m) = S (S n0 + m)) (n0 + S m = S (n0 + m) <-> S (n0 + S m) = S (S (n0 + m)))`.
        - ▫️ Assume `S n0 + m = S (n0 + m)` (lemma).
          - ✅ We deduce `S (n0 + S m) = S (S n0 + m) <-> S (n0 + S m) = S (S (n0 + m))`.
            - ✅ We deduce `S (S n0 + m) = S (S (n0 + m))`.
              - ✅ By lemma we have `S n0 + m = S (n0 + m)`.
              - ✅ In particular `S n0 + m = S (n0 + m) -> S (S n0 + m) = S (S (n0 + m))`.
                - ❌ Using succ_wd we get `Morphisms.Proper (Morphisms.respectful eq eq) S` .*by exact @succ_wd*

                  <details><summary>not proved</summary>

                  ```
                  1 goal
                    
                    n, m, n0 : nat
                    H : forall x y : nat, x = y -> x + S m = S (x + m) <-> y + S m = S (y + m)
                    H0 : 0 + S m = S (0 + m)
                    H1 : S n0 + S m = S (n0 + S m)
                    H2 : S n0 + m = S (n0 + m)
                    H3 : n0 + S m = S (n0 + m) <-> S (n0 + S m) = S (S (n0 + m))
                    H4, H5 : S n0 + m = S (n0 + m)
                    ============================
                    Morphisms.Proper (Morphisms.respectful eq eq) S
                  
                  File "./cyp_ko_133.v", line 4, characters 0-92:
                  Error: No applicable tactic.
                  ```

                  </details>
            - ❌ In particular `S (S n0 + m) = S (S (n0 + m)) -> S (n0 + S m) = S (S n0 + m) <-> S (n0 + S m) = S (S (n0 + m))`.

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
                  CYP-OK 19
                  CYP-KO 20
                  CYP-OK 21
                  CYP-OK 22
                  CYP-OK 23
                  CYP-OK 24
                  CYP-KO 25
                  CYP-OK 26
                  CYP-OK 27
                  CYP-OK 39
                  CYP-KO 40
                  CYP-OK 41
                  CYP-OK 42
                  CYP-OK 43
                  CYP-OK 44
                  CYP-OK 53
                  CYP-OK 54
                  CYP-OK 55
                  CYP-KO 56
                  CYP-KO 57
                  CYP-OK 58
                  CYP-OK 59
                  CYP-OK 60
                  CYP-OK 61
                  CYP-OK 62
                  CYP-OK 63
                  CYP-OK 64
                  CYP-OK 65
                  CYP-KO 66
                  CYP-OK 67
                  CYP-KO 68
                  CYP-OK 69
                  CYP-OK 78
                  CYP-KO 79
                  CYP-OK 80
                  CYP-OK 81
                  CYP-OK 90
                  CYP-OK 91
                  CYP-OK 92
                  CYP-KO 93
                  CYP-OK 94
                  CYP-OK 95
                  CYP-OK 104
                  CYP-OK 105
                  CYP-OK 106
                  CYP-OK 107
                  CYP-OK 108
                  CYP-KO 109
                  CYP-OK 110
                  CYP-KO 111
                  CYP-OK 112
                  CYP-KO 113
                  CYP-OK 114
                  CYP-KO 115
                  CYP-KO 116
                  CYP-OK 117
                  CYP-OK 118
                  CYP-OK 119
                  CYP-OK 120
                  CYP-KO 121
                  CYP-KO 122
                  CYP-OK 123
                  CYP-OK 124
                  CYP-KO 125
                  CYP-OK 126
                  CYP-OK 127
                  CYP-OK 128
                  CYP-OK 129
                  CYP-OK 130
                  CYP-OK 131
                  CYP-OK 132
                  CYP-KO 133
                  CYP-OK 134
                  CYP-OK 135
                  File "./cyp_check.v", line 326, characters 332-359:
                  Error: Cannot infer the implicit parameter A of RelationClasses.Equivalence
                  whose type is "Type" in environment:
                  n, m, n0 : nat
                  
                  
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
              - ❌ In particular `RelationClasses.PER eq -> forall x : nat, Morphisms.Proper (Morphisms.respectful eq iff) (eq x)`.

                <details><summary>Rocq error</summary>

                ```
                This step does not type-check because an earlier step does not: see the first Rocq error above.
                ```

                </details>
                - ❌ Using per_partial_app_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> forall x : A, Morphisms.Proper (Morphisms.respectful R iff) (R x)` .*by exact @per_partial_app_morphism*

                  <details><summary>Rocq error</summary>

                  ```
                  CYP-KO 1
                  CYP-OK 2
                  CYP-KO 3
                  CYP-KO 4
                  CYP-OK 5
                  CYP-OK 6
                  CYP-OK 7
                  CYP-OK 19
                  CYP-KO 20
                  CYP-OK 21
                  CYP-OK 22
                  CYP-OK 23
                  CYP-OK 24
                  CYP-KO 25
                  CYP-OK 26
                  CYP-OK 27
                  CYP-OK 39
                  CYP-KO 40
                  CYP-OK 41
                  CYP-OK 42
                  CYP-OK 43
                  CYP-OK 44
                  CYP-OK 53
                  CYP-OK 54
                  CYP-OK 55
                  CYP-KO 56
                  CYP-KO 57
                  CYP-OK 58
                  CYP-OK 59
                  CYP-OK 60
                  CYP-OK 61
                  CYP-OK 62
                  CYP-OK 63
                  CYP-OK 64
                  CYP-OK 65
                  CYP-KO 66
                  CYP-OK 67
                  CYP-KO 68
                  CYP-OK 69
                  CYP-OK 78
                  CYP-KO 79
                  CYP-OK 80
                  CYP-OK 81
                  CYP-OK 90
                  CYP-OK 91
                  CYP-OK 92
                  CYP-KO 93
                  CYP-OK 94
                  CYP-OK 95
                  CYP-OK 104
                  CYP-OK 105
                  CYP-OK 106
                  CYP-OK 107
                  CYP-OK 108
                  CYP-KO 109
                  CYP-OK 110
                  CYP-KO 111
                  CYP-OK 112
                  CYP-KO 113
                  CYP-OK 114
                  CYP-KO 115
                  CYP-KO 116
                  CYP-OK 117
                  CYP-OK 118
                  CYP-OK 119
                  CYP-OK 120
                  CYP-KO 121
                  CYP-KO 122
                  CYP-OK 123
                  CYP-OK 124
                  CYP-KO 125
                  CYP-OK 126
                  CYP-OK 127
                  CYP-OK 128
                  CYP-OK 129
                  CYP-OK 130
                  CYP-OK 131
                  CYP-OK 132
                  CYP-KO 133
                  CYP-OK 134
                  CYP-OK 135
                  File "./cyp_check.v", line 326, characters 332-351:
                  Error: Cannot infer the implicit parameter A of RelationClasses.PER whose
                  type is "Type" in environment:
                  n, m, n0 : nat
                  
                  
                  ```

                  </details>
              - ❌ We deduce `forall x : nat, Morphisms.Proper (Morphisms.respectful eq iff) (eq x)`.

                <details><summary>Rocq error</summary>

                ```
                This step does not type-check because an earlier step does not: see the first Rocq error above.
                ```

                </details>
          - ✅ In particular `S (n0 + S m) = S (S n0 + m) <-> S (n0 + S m) = S (S (n0 + m)) -> Basics.flip Basics.impl (n0 + S m = S (n0 + m) <-> S (n0 + S m) = S (S n0 + m)) (n0 + S m = S (n0 + m) <-> S (n0 + S m) = S (S (n0 + m)))`.
            - ✅ We deduce `RelationClasses.PER iff`.
              - ❌ Using iff_equivalence we get `RelationClasses.Equivalence iff` .*by exact @iff_equivalence*

                <details><summary>not proved</summary>

                ```
                1 goal
                  
                  n, m, n0 : nat
                  H : forall x y : nat, x = y -> x + S m = S (x + m) <-> y + S m = S (y + m)
                  H0 : 0 + S m = S (0 + m)
                  H1 : S n0 + S m = S (n0 + S m)
                  H2 : S n0 + m = S (n0 + m)
                  H3 : n0 + S m = S (n0 + m) <-> S (n0 + S m) = S (S (n0 + m))
                  H4 : S n0 + m = S (n0 + m)
                  H5 : S (n0 + S m) = S (S n0 + m) <-> S (n0 + S m) = S (S (n0 + m))
                  ============================
                  RelationClasses.Equivalence iff
                
                File "./cyp_ko_145.v", line 4, characters 0-108:
                Error: No applicable tactic.
                ```

                </details>
              - ✅ In particular `RelationClasses.Equivalence iff -> RelationClasses.PER iff`.
                - ❌ Using Equivalence_PER we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R` .*by exact @Equivalence_PER*

                  <details><summary>not proved</summary>

                  ```
                  1 goal
                    
                    n, m, n0 : nat
                    H : forall x y : nat, x = y -> x + S m = S (x + m) <-> y + S m = S (y + m)
                    H0 : 0 + S m = S (0 + m)
                    H1 : S n0 + S m = S (n0 + S m)
                    H2 : S n0 + m = S (n0 + m)
                    H3 : n0 + S m = S (n0 + m) <-> S (n0 + S m) = S (S (n0 + m))
                    H4 : S n0 + m = S (n0 + m)
                    H5 : S (n0 + S m) = S (S n0 + m) <-> S (n0 + S m) = S (S (n0 + m))
                    H6 : RelationClasses.Equivalence iff
                    A : Type
                    R : Relation_Definitions.relation A
                    H7 : RelationClasses.Equivalence R
                    ============================
                    RelationClasses.PER R
                  
                  File "./cyp_ko_146.v", line 4, characters 0-108:
                  Error: No applicable tactic.
                  ```

                  </details>
            - ✅ In particular `RelationClasses.PER iff -> forall x : Prop, Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (iff x)`.
              - ❌ Using trans_sym_co_inv_impl_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> forall x : A, Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)` .*by exact @trans_sym_co_inv_impl_morphism*

                <details><summary>not proved</summary>

                ```
                1 goal
                  
                  n, m, n0 : nat
                  H : forall x y : nat, x = y -> x + S m = S (x + m) <-> y + S m = S (y + m)
                  H0 : 0 + S m = S (0 + m)
                  H1 : S n0 + S m = S (n0 + S m)
                  H2 : S n0 + m = S (n0 + m)
                  H3 : n0 + S m = S (n0 + m) <-> S (n0 + S m) = S (S (n0 + m))
                  H4 : S n0 + m = S (n0 + m)
                  H5 : S (n0 + S m) = S (S n0 + m) <-> S (n0 + S m) = S (S (n0 + m))
                  H6 : RelationClasses.PER iff
                  A : Type
                  R : Relation_Definitions.relation A
                  H7 : RelationClasses.PER R
                  x : A
                  ============================
                  Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)
                
                File "./cyp_ko_149.v", line 4, characters 0-138:
                Error: No applicable tactic.
                ```

                </details>
            - ✅ We deduce `forall x : Prop, Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (iff x)`.
          - ✅ We deduce `Basics.flip Basics.impl (n0 + S m = S (n0 + m) <-> S (n0 + S m) = S (S n0 + m)) (n0 + S m = S (n0 + m) <-> S (n0 + S m) = S (S (n0 + m)))`.
    - ✅ We have proved `S n0 + S m = S (n0 + S m) -> Basics.flip Basics.impl (n0 + S m = S (n0 + m) <-> S n0 + S m = S (S n0 + m)) (n0 + S m = S (n0 + m) <-> S (n0 + S m) = S (S n0 + m))`.
      - ▫️ Assume `S n0 + S m = S (n0 + S m)` (lemma).
        - ✅ We deduce `S n0 + S m = S (S n0 + m) <-> S (n0 + S m) = S (S n0 + m)`.
          - ❌ In particular `Morphisms.ProperProxy eq (S (S n0 + m))`.

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
                  CYP-OK 19
                  CYP-KO 20
                  CYP-OK 21
                  CYP-OK 22
                  CYP-OK 23
                  CYP-OK 24
                  CYP-KO 25
                  CYP-OK 26
                  CYP-OK 27
                  CYP-OK 39
                  CYP-KO 40
                  CYP-OK 41
                  CYP-OK 42
                  CYP-OK 43
                  CYP-OK 44
                  CYP-OK 53
                  CYP-OK 54
                  CYP-OK 55
                  CYP-KO 56
                  CYP-KO 57
                  CYP-OK 58
                  CYP-OK 59
                  CYP-OK 60
                  CYP-OK 61
                  CYP-OK 62
                  CYP-OK 63
                  CYP-OK 64
                  CYP-OK 65
                  CYP-KO 66
                  CYP-OK 67
                  CYP-KO 68
                  CYP-OK 69
                  CYP-OK 78
                  CYP-KO 79
                  CYP-OK 80
                  CYP-OK 81
                  CYP-OK 90
                  CYP-OK 91
                  CYP-OK 92
                  CYP-KO 93
                  CYP-OK 94
                  CYP-OK 95
                  CYP-OK 104
                  CYP-OK 105
                  CYP-OK 106
                  CYP-OK 107
                  CYP-OK 108
                  CYP-KO 109
                  CYP-OK 110
                  CYP-KO 111
                  CYP-OK 112
                  CYP-KO 113
                  CYP-OK 114
                  CYP-KO 115
                  CYP-KO 116
                  CYP-OK 117
                  CYP-OK 118
                  CYP-OK 119
                  CYP-OK 120
                  CYP-KO 121
                  CYP-KO 122
                  CYP-OK 123
                  CYP-OK 124
                  CYP-KO 125
                  CYP-OK 126
                  CYP-OK 127
                  CYP-OK 128
                  CYP-OK 129
                  CYP-OK 130
                  CYP-OK 131
                  CYP-OK 132
                  CYP-KO 133
                  CYP-OK 134
                  CYP-OK 135
                  CYP-OK 144
                  CYP-KO 145
                  CYP-KO 146
                  CYP-OK 147
                  CYP-OK 148
                  CYP-KO 149
                  CYP-OK 150
                  CYP-OK 151
                  CYP-OK 152
                  CYP-OK 153
                  CYP-OK 154
                  CYP-OK 155
                  File "./cyp_check.v", line 374, characters 268-295:
                  Error: Cannot infer the implicit parameter A of RelationClasses.Equivalence
                  whose type is "Type" in environment:
                  n, m, n0 : nat
                  
                  
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
                  CYP-OK 19
                  CYP-KO 20
                  CYP-OK 21
                  CYP-OK 22
                  CYP-OK 23
                  CYP-OK 24
                  CYP-KO 25
                  CYP-OK 26
                  CYP-OK 27
                  CYP-OK 39
                  CYP-KO 40
                  CYP-OK 41
                  CYP-OK 42
                  CYP-OK 43
                  CYP-OK 44
                  CYP-OK 53
                  CYP-OK 54
                  CYP-OK 55
                  CYP-KO 56
                  CYP-KO 57
                  CYP-OK 58
                  CYP-OK 59
                  CYP-OK 60
                  CYP-OK 61
                  CYP-OK 62
                  CYP-OK 63
                  CYP-OK 64
                  CYP-OK 65
                  CYP-KO 66
                  CYP-OK 67
                  CYP-KO 68
                  CYP-OK 69
                  CYP-OK 78
                  CYP-KO 79
                  CYP-OK 80
                  CYP-OK 81
                  CYP-OK 90
                  CYP-OK 91
                  CYP-OK 92
                  CYP-KO 93
                  CYP-OK 94
                  CYP-OK 95
                  CYP-OK 104
                  CYP-OK 105
                  CYP-OK 106
                  CYP-OK 107
                  CYP-OK 108
                  CYP-KO 109
                  CYP-OK 110
                  CYP-KO 111
                  CYP-OK 112
                  CYP-KO 113
                  CYP-OK 114
                  CYP-KO 115
                  CYP-KO 116
                  CYP-OK 117
                  CYP-OK 118
                  CYP-OK 119
                  CYP-OK 120
                  CYP-KO 121
                  CYP-KO 122
                  CYP-OK 123
                  CYP-OK 124
                  CYP-KO 125
                  CYP-OK 126
                  CYP-OK 127
                  CYP-OK 128
                  CYP-OK 129
                  CYP-OK 130
                  CYP-OK 131
                  CYP-OK 132
                  CYP-KO 133
                  CYP-OK 134
                  CYP-OK 135
                  CYP-OK 144
                  CYP-KO 145
                  CYP-KO 146
                  CYP-OK 147
                  CYP-OK 148
                  CYP-KO 149
                  CYP-OK 150
                  CYP-OK 151
                  CYP-OK 152
                  CYP-OK 153
                  CYP-OK 154
                  CYP-OK 155
                  File "./cyp_check.v", line 374, characters 268-293:
                  Error: Cannot infer the implicit parameter A of RelationClasses.Reflexive
                  whose type is "Type" in environment:
                  n, m, n0 : nat
                  
                  
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
                CYP-OK 19
                CYP-KO 20
                CYP-OK 21
                CYP-OK 22
                CYP-OK 23
                CYP-OK 24
                CYP-KO 25
                CYP-OK 26
                CYP-OK 27
                CYP-OK 39
                CYP-KO 40
                CYP-OK 41
                CYP-OK 42
                CYP-OK 43
                CYP-OK 44
                CYP-OK 53
                CYP-OK 54
                CYP-OK 55
                CYP-KO 56
                CYP-KO 57
                CYP-OK 58
                CYP-OK 59
                CYP-OK 60
                CYP-OK 61
                CYP-OK 62
                CYP-OK 63
                CYP-OK 64
                CYP-OK 65
                CYP-KO 66
                CYP-OK 67
                CYP-KO 68
                CYP-OK 69
                CYP-OK 78
                CYP-KO 79
                CYP-OK 80
                CYP-OK 81
                CYP-OK 90
                CYP-OK 91
                CYP-OK 92
                CYP-KO 93
                CYP-OK 94
                CYP-OK 95
                CYP-OK 104
                CYP-OK 105
                CYP-OK 106
                CYP-OK 107
                CYP-OK 108
                CYP-KO 109
                CYP-OK 110
                CYP-KO 111
                CYP-OK 112
                CYP-KO 113
                CYP-OK 114
                CYP-KO 115
                CYP-KO 116
                CYP-OK 117
                CYP-OK 118
                CYP-OK 119
                CYP-OK 120
                CYP-KO 121
                CYP-KO 122
                CYP-OK 123
                CYP-OK 124
                CYP-KO 125
                CYP-OK 126
                CYP-OK 127
                CYP-OK 128
                CYP-OK 129
                CYP-OK 130
                CYP-OK 131
                CYP-OK 132
                CYP-KO 133
                CYP-OK 134
                CYP-OK 135
                CYP-OK 144
                CYP-KO 145
                CYP-KO 146
                CYP-OK 147
                CYP-OK 148
                CYP-KO 149
                CYP-OK 150
                CYP-OK 151
                CYP-OK 152
                CYP-OK 153
                CYP-OK 154
                CYP-OK 155
                File "./cyp_check.v", line 374, characters 268-292:
                Error: Cannot infer the implicit parameter A of Morphisms.ReflexiveProxy
                whose type is "Type" in environment:
                n, m, n0 : nat
                
                
                ```

                </details>
            - ❌ We deduce `forall x : nat, Morphisms.ProperProxy eq x`.

              <details><summary>Rocq error</summary>

              ```
              This step does not type-check because an earlier step does not: see the first Rocq error above.
              ```

              </details>
          - ✅ In particular `S (S n0 + m) = S (S n0 + m) -> S n0 + S m = S (S n0 + m) <-> S (n0 + S m) = S (S n0 + m)`.
            - ✅ By lemma we have `S n0 + S m = S (n0 + S m)`.
            - ❌ In particular `S n0 + S m = S (n0 + S m) -> Morphisms.respectful eq iff (eq (S n0 + S m)) (eq (S (n0 + S m)))`.

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
                  CYP-OK 19
                  CYP-KO 20
                  CYP-OK 21
                  CYP-OK 22
                  CYP-OK 23
                  CYP-OK 24
                  CYP-KO 25
                  CYP-OK 26
                  CYP-OK 27
                  CYP-OK 39
                  CYP-KO 40
                  CYP-OK 41
                  CYP-OK 42
                  CYP-OK 43
                  CYP-OK 44
                  CYP-OK 53
                  CYP-OK 54
                  CYP-OK 55
                  CYP-KO 56
                  CYP-KO 57
                  CYP-OK 58
                  CYP-OK 59
                  CYP-OK 60
                  CYP-OK 61
                  CYP-OK 62
                  CYP-OK 63
                  CYP-OK 64
                  CYP-OK 65
                  CYP-KO 66
                  CYP-OK 67
                  CYP-KO 68
                  CYP-OK 69
                  CYP-OK 78
                  CYP-KO 79
                  CYP-OK 80
                  CYP-OK 81
                  CYP-OK 90
                  CYP-OK 91
                  CYP-OK 92
                  CYP-KO 93
                  CYP-OK 94
                  CYP-OK 95
                  CYP-OK 104
                  CYP-OK 105
                  CYP-OK 106
                  CYP-OK 107
                  CYP-OK 108
                  CYP-KO 109
                  CYP-OK 110
                  CYP-KO 111
                  CYP-OK 112
                  CYP-KO 113
                  CYP-OK 114
                  CYP-KO 115
                  CYP-KO 116
                  CYP-OK 117
                  CYP-OK 118
                  CYP-OK 119
                  CYP-OK 120
                  CYP-KO 121
                  CYP-KO 122
                  CYP-OK 123
                  CYP-OK 124
                  CYP-KO 125
                  CYP-OK 126
                  CYP-OK 127
                  CYP-OK 128
                  CYP-OK 129
                  CYP-OK 130
                  CYP-OK 131
                  CYP-OK 132
                  CYP-KO 133
                  CYP-OK 134
                  CYP-OK 135
                  CYP-OK 144
                  CYP-KO 145
                  CYP-KO 146
                  CYP-OK 147
                  CYP-OK 148
                  CYP-KO 149
                  CYP-OK 150
                  CYP-OK 151
                  CYP-OK 152
                  CYP-OK 153
                  CYP-OK 154
                  CYP-OK 155
                  CYP-OK 167
                  File "./cyp_check.v", line 378, characters 348-375:
                  Error: Cannot infer the implicit parameter A of RelationClasses.Equivalence
                  whose type is "Type" in environment:
                  n, m, n0 : nat
                  
                  
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
                  CYP-OK 19
                  CYP-KO 20
                  CYP-OK 21
                  CYP-OK 22
                  CYP-OK 23
                  CYP-OK 24
                  CYP-KO 25
                  CYP-OK 26
                  CYP-OK 27
                  CYP-OK 39
                  CYP-KO 40
                  CYP-OK 41
                  CYP-OK 42
                  CYP-OK 43
                  CYP-OK 44
                  CYP-OK 53
                  CYP-OK 54
                  CYP-OK 55
                  CYP-KO 56
                  CYP-KO 57
                  CYP-OK 58
                  CYP-OK 59
                  CYP-OK 60
                  CYP-OK 61
                  CYP-OK 62
                  CYP-OK 63
                  CYP-OK 64
                  CYP-OK 65
                  CYP-KO 66
                  CYP-OK 67
                  CYP-KO 68
                  CYP-OK 69
                  CYP-OK 78
                  CYP-KO 79
                  CYP-OK 80
                  CYP-OK 81
                  CYP-OK 90
                  CYP-OK 91
                  CYP-OK 92
                  CYP-KO 93
                  CYP-OK 94
                  CYP-OK 95
                  CYP-OK 104
                  CYP-OK 105
                  CYP-OK 106
                  CYP-OK 107
                  CYP-OK 108
                  CYP-KO 109
                  CYP-OK 110
                  CYP-KO 111
                  CYP-OK 112
                  CYP-KO 113
                  CYP-OK 114
                  CYP-KO 115
                  CYP-KO 116
                  CYP-OK 117
                  CYP-OK 118
                  CYP-OK 119
                  CYP-OK 120
                  CYP-KO 121
                  CYP-KO 122
                  CYP-OK 123
                  CYP-OK 124
                  CYP-KO 125
                  CYP-OK 126
                  CYP-OK 127
                  CYP-OK 128
                  CYP-OK 129
                  CYP-OK 130
                  CYP-OK 131
                  CYP-OK 132
                  CYP-KO 133
                  CYP-OK 134
                  CYP-OK 135
                  CYP-OK 144
                  CYP-KO 145
                  CYP-KO 146
                  CYP-OK 147
                  CYP-OK 148
                  CYP-KO 149
                  CYP-OK 150
                  CYP-OK 151
                  CYP-OK 152
                  CYP-OK 153
                  CYP-OK 154
                  CYP-OK 155
                  CYP-OK 167
                  File "./cyp_check.v", line 378, characters 348-367:
                  Error: Cannot infer the implicit parameter A of RelationClasses.PER whose
                  type is "Type" in environment:
                  n, m, n0 : nat
                  
                  
                  ```

                  </details>
              - ❌ We deduce `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq iff)) eq`.

                <details><summary>Rocq error</summary>

                ```
                This step does not type-check because an earlier step does not: see the first Rocq error above.
                ```

                </details>
            - ✅ We deduce `Morphisms.respectful eq iff (eq (S n0 + S m)) (eq (S (n0 + S m)))`.
        - ✅ In particular `S n0 + S m = S (S n0 + m) <-> S (n0 + S m) = S (S n0 + m) -> Basics.flip Basics.impl (n0 + S m = S (n0 + m) <-> S n0 + S m = S (S n0 + m)) (n0 + S m = S (n0 + m) <-> S (n0 + S m) = S (S n0 + m))`.
          - ✅ We deduce `RelationClasses.PER iff`.
            - ❌ Using iff_equivalence we get `RelationClasses.Equivalence iff` .*by exact @iff_equivalence*

              <details><summary>not proved</summary>

              ```
              1 goal
                
                n, m, n0 : nat
                H : forall x y : nat, x = y -> x + S m = S (x + m) <-> y + S m = S (y + m)
                H0 : 0 + S m = S (0 + m)
                H1 : S n0 + S m = S (n0 + S m)
                H2 : n0 + S m = S (n0 + m) <-> S (n0 + S m) = S (S n0 + m)
                H3 : S n0 + S m = S (n0 + S m)
                H4 : S n0 + S m = S (S n0 + m) <-> S (n0 + S m) = S (S n0 + m)
                ============================
                RelationClasses.Equivalence iff
              
              File "./cyp_ko_179.v", line 4, characters 0-108:
              Error: No applicable tactic.
              ```

              </details>
            - ✅ In particular `RelationClasses.Equivalence iff -> RelationClasses.PER iff`.
              - ❌ Using Equivalence_PER we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R` .*by exact @Equivalence_PER*

                <details><summary>not proved</summary>

                ```
                1 goal
                  
                  n, m, n0 : nat
                  H : forall x y : nat, x = y -> x + S m = S (x + m) <-> y + S m = S (y + m)
                  H0 : 0 + S m = S (0 + m)
                  H1 : S n0 + S m = S (n0 + S m)
                  H2 : n0 + S m = S (n0 + m) <-> S (n0 + S m) = S (S n0 + m)
                  H3 : S n0 + S m = S (n0 + S m)
                  H4 : S n0 + S m = S (S n0 + m) <-> S (n0 + S m) = S (S n0 + m)
                  H5 : RelationClasses.Equivalence iff
                  A : Type
                  R : Relation_Definitions.relation A
                  H6 : RelationClasses.Equivalence R
                  ============================
                  RelationClasses.PER R
                
                File "./cyp_ko_180.v", line 4, characters 0-108:
                Error: No applicable tactic.
                ```

                </details>
          - ✅ In particular `RelationClasses.PER iff -> forall x : Prop, Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (iff x)`.
            - ❌ Using trans_sym_co_inv_impl_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> forall x : A, Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)` .*by exact @trans_sym_co_inv_impl_morphism*

              <details><summary>not proved</summary>

              ```
              1 goal
                
                n, m, n0 : nat
                H : forall x y : nat, x = y -> x + S m = S (x + m) <-> y + S m = S (y + m)
                H0 : 0 + S m = S (0 + m)
                H1 : S n0 + S m = S (n0 + S m)
                H2 : n0 + S m = S (n0 + m) <-> S (n0 + S m) = S (S n0 + m)
                H3 : S n0 + S m = S (n0 + S m)
                H4 : S n0 + S m = S (S n0 + m) <-> S (n0 + S m) = S (S n0 + m)
                H5 : RelationClasses.PER iff
                A : Type
                R : Relation_Definitions.relation A
                H6 : RelationClasses.PER R
                x : A
                ============================
                Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)
              
              File "./cyp_ko_183.v", line 4, characters 0-138:
              Error: No applicable tactic.
              ```

              </details>
          - ✅ We deduce `forall x : Prop, Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (iff x)`.
        - ✅ We deduce `Basics.flip Basics.impl (n0 + S m = S (n0 + m) <-> S n0 + S m = S (S n0 + m)) (n0 + S m = S (n0 + m) <-> S (n0 + S m) = S (S n0 + m))`.
    - ✅ We deduce `n0 + S m = S (n0 + m) <-> S n0 + S m = S (S n0 + m)`.
- ✅ In particular `Morphisms.Proper (Morphisms.respectful eq iff) (fun t : nat => t + S m = S (t + m)) -> 0 + S m = S (0 + m) -> (forall n0 : nat, n0 + S m = S (n0 + m) <-> S n0 + S m = S (S n0 + m)) -> forall n0 : nat, n0 + S m = S (n0 + m)`.
  - ❌ Using bi_induction we get `forall A : nat -> Prop, Morphisms.Proper (Morphisms.respectful eq iff) A -> A 0 -> (forall n0 : nat, A n0 <-> A (S n0)) -> forall n0 : nat, A n0` .*by exact @bi_induction*

    <details><summary>not proved</summary>

    ```
    1 goal
      
      n, m : nat
      H : forall x y : nat, x = y -> x + S m = S (x + m) <-> y + S m = S (y + m)
      H0 : 0 + S m = S (0 + m)
      H1 : forall n0 : nat, n0 + S m = S (n0 + m) <-> S n0 + S m = S (S n0 + m)
      A : nat -> Prop
      H2 : Morphisms.Proper (Morphisms.respectful eq iff) A
      H3 : A 0
      H4 : forall n0 : nat, A n0 <-> A (S n0)
      n0 : nat
      ============================
      A n0
    
    File "./cyp_ko_191.v", line 4, characters 0-102:
    Error: No applicable tactic.
    ```

    </details>
- ✅ We deduce `forall n0 : nat, n0 + S m = S (n0 + m)`.
- ✅ In particular `n + S m = S (n + m)`.

