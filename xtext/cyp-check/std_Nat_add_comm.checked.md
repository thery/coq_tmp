<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# Nat.add_comm

✅ Let `n m : nat`. We prove `n + m = m + n`.

- ✅ Thus we have `forall x y : nat, x = y -> x + m = m + x <-> y + m = m + y`.
  - ▫️ Let us choose arbitrarily `x : nat`, `y : nat`.
    - ▫️ Assume `x = y` (H).
      - ✅ In particular `Morphisms.ProperProxy eq (y + m = m + y)`.
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
      - ✅ In particular `y + m = m + y <-> y + m = m + y`.
        - ❌ Using iff_Reflexive we get `RelationClasses.Reflexive iff` .*by exact @iff_Reflexive*

          <details><summary>not proved</summary>

          ```
          1 goal
            
            n, m, x, y : nat
            H : x = y
            H0 : Morphisms.ProperProxy eq (y + m = m + y)
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
              H0 : Morphisms.ProperProxy eq (y + m = m + y)
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
      - ✅ In particular `(y + m = m + y) = (y + m = m + y) -> Basics.flip Basics.impl (x + m = m + x <-> y + m = m + y) (y + m = m + y <-> y + m = m + y)`.
        - ✅ We deduce `x + m = m + x <-> y + m = m + y`.
          - ✅ We deduce `m + x = m + y`.
            - ✅ By H we have `x = y`.
            - ✅ In particular `x = y -> m + x = m + y`.
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
                      CYP-OK 8
                      File "./cyp_check.v", line 34, characters 158-185:
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
                      CYP-OK 8
                      File "./cyp_check.v", line 34, characters 158-183:
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
                    CYP-OK 8
                    File "./cyp_check.v", line 34, characters 158-182:
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
              - ✅ In particular `Morphisms.ProperProxy eq m -> Morphisms.Proper (Morphisms.respectful eq eq) (Nat.add m)`.
                - ❌ Using add_wd we get `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Init.Nat.add` .*by exact @add_wd*

                  <details><summary>not proved</summary>

                  ```
                  1 goal
                    
                    n, m, x, y : nat
                    H : x = y
                    H0 : Morphisms.ProperProxy eq (y + m = m + y)
                    H1 : y + m = m + y <-> y + m = m + y
                    H2 : x = y
                    H3 : Morphisms.ProperProxy eq m
                    ============================
                    Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq))
                      Init.Nat.add
                  
                  File "./cyp_ko_20.v", line 4, characters 0-90:
                  Error: No applicable tactic.
                  ```

                  </details>
                - ✅ In particular `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Nat.add -> forall x0 : nat, Morphisms.ProperProxy eq x0 -> Morphisms.Proper (Morphisms.respectful eq eq) (Nat.add x0)`.
                  - ❌ Using Reflexive_partial_app_morphism we get `forall (A B : Type) (R : Relation_Definitions.relation A) (R' : Relation_Definitions.relation B) (m0 : A -> B), Morphisms.Proper (Morphisms.respectful R R') m0 -> forall x0 : A, Morphisms.ProperProxy R x0 -> Morphisms.Proper R' (m0 x0)` .*by exact @Reflexive_partial_app_morphism*

                    <details><summary>not proved</summary>

                    ```
                    1 goal
                      
                      n, m, x, y : nat
                      H : x = y
                      H0 : Morphisms.ProperProxy eq (y + m = m + y)
                      H1 : y + m = m + y <-> y + m = m + y
                      H2 : x = y
                      H3 : Morphisms.ProperProxy eq m
                      H4 :
                        Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq))
                          Init.Nat.add
                      A : Type
                      B : Type
                      R : Relation_Definitions.relation A
                      R' : Relation_Definitions.relation B
                      m0 : A -> B
                      H5 : Morphisms.Proper (Morphisms.respectful R R') m0
                      x0 : A
                      H6 : Morphisms.ProperProxy R x0
                      ============================
                      Morphisms.Proper R' (m0 x0)
                    
                    File "./cyp_ko_21.v", line 4, characters 0-138:
                    Error: No applicable tactic.
                    ```

                    </details>
                - ✅ We deduce `forall x0 : nat, Morphisms.ProperProxy eq x0 -> Morphisms.Proper (Morphisms.respectful eq eq) (Nat.add x0)`.
              - ✅ We deduce `Morphisms.Proper (Morphisms.respectful eq eq) (Nat.add m)`.
          - ✅ In particular `m + x = m + y -> x + m = m + x <-> y + m = m + y`.
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
                      CYP-OK 8
                      CYP-KO 20
                      CYP-KO 21
                      CYP-OK 22
                      CYP-OK 23
                      CYP-OK 24
                      CYP-OK 25
                      CYP-OK 26
                      CYP-OK 27
                      File "./cyp_check.v", line 66, characters 166-193:
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
                      CYP-OK 8
                      CYP-KO 20
                      CYP-KO 21
                      CYP-OK 22
                      CYP-OK 23
                      CYP-OK 24
                      CYP-OK 25
                      CYP-OK 26
                      CYP-OK 27
                      File "./cyp_check.v", line 66, characters 166-191:
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
                    CYP-OK 8
                    CYP-KO 20
                    CYP-KO 21
                    CYP-OK 22
                    CYP-OK 23
                    CYP-OK 24
                    CYP-OK 25
                    CYP-OK 26
                    CYP-OK 27
                    File "./cyp_check.v", line 66, characters 166-190:
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
                      H0 : Morphisms.ProperProxy eq (y + m = m + y)
                      H1 : y + m = m + y <-> y + m = m + y
                      H2 : m + x = m + y
                      H3 : Morphisms.ProperProxy eq m
                      H4 : x = y
                      ============================
                      Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq))
                        Init.Nat.add
                    
                    File "./cyp_ko_40.v", line 4, characters 0-90:
                    Error: No applicable tactic.
                    ```

                    </details>
                - ✅ We deduce `Morphisms.respectful eq eq (Init.Nat.add x) (Init.Nat.add y)`.
            - ❌ In particular `x + m = y + m -> Morphisms.respectful eq iff (eq (x + m)) (eq (y + m))`.

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
                  CYP-KO 20
                  CYP-KO 21
                  CYP-OK 22
                  CYP-OK 23
                  CYP-OK 24
                  CYP-OK 25
                  CYP-OK 26
                  CYP-OK 27
                  CYP-OK 39
                  CYP-KO 40
                  CYP-OK 41
                  CYP-OK 42
                  CYP-OK 43
                  CYP-OK 44
                  File "./cyp_check.v", line 90, characters 187-214:
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
                  CYP-OK 8
                  CYP-KO 20
                  CYP-KO 21
                  CYP-OK 22
                  CYP-OK 23
                  CYP-OK 24
                  CYP-OK 25
                  CYP-OK 26
                  CYP-OK 27
                  CYP-OK 39
                  CYP-KO 40
                  CYP-OK 41
                  CYP-OK 42
                  CYP-OK 43
                  CYP-OK 44
                  File "./cyp_check.v", line 90, characters 187-206:
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
            - ✅ We deduce `Morphisms.respectful eq iff (eq (x + m)) (eq (y + m))`.
        - ✅ In particular `x + m = m + x <-> y + m = m + y -> Morphisms.respectful eq (Basics.flip Basics.impl) (iff (x + m = m + x)) (iff (y + m = m + y))`.
          - ❌ Using iff_Transitive we get `RelationClasses.Transitive iff` .*by exact @iff_Transitive*

            <details><summary>not proved</summary>

            ```
            1 goal
              
              n, m, x, y : nat
              H : x = y
              H0 : Morphisms.ProperProxy eq (y + m = m + y)
              H1 : y + m = m + y <-> y + m = m + y
              H2 : x + m = m + x <-> y + m = m + y
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
                H0 : Morphisms.ProperProxy eq (y + m = m + y)
                H1 : y + m = m + y <-> y + m = m + y
                H2 : x + m = m + x <-> y + m = m + y
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
        - ✅ We deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (iff (x + m = m + x)) (iff (y + m = m + y))`.
      - ✅ We deduce `x + m = m + x <-> y + m = m + y`.
    - ✅ We have proved `x = y -> x + m = m + x <-> y + m = m + y`.
- ✅ We deduce `0 + m = m + 0`.
  - ✅ In particular `m + 0 = m`.
    - ❌ Using add_0_r we get `forall n0 : nat, n0 + 0 = n0` .*by exact @add_0_r*

      <details><summary>not proved</summary>

      ```
      1 goal
        
        n, m : nat
        H : forall x y : nat, x = y -> x + m = m + x <-> y + m = m + y
        n0 : nat
        ============================
        n0 + 0 = n0
      
      File "./cyp_ko_66.v", line 4, characters 0-92:
      Error: No applicable tactic.
      ```

      </details>
  - ✅ We deduce `0 + m = m`.
    - ✅ In particular `0 + m = m`.
      - ❌ Using add_0_l we get `forall n0 : nat, 0 + n0 = n0` .*by exact @add_0_l*

        <details><summary>not proved</summary>

        ```
        1 goal
          
          n, m : nat
          H : forall x y : nat, x = y -> x + m = m + x <-> y + m = m + y
          H0 : m + 0 = m
          n0 : nat
          ============================
          0 + n0 = n0
        
        File "./cyp_ko_68.v", line 4, characters 0-92:
        Error: No applicable tactic.
        ```

        </details>
    - ❌ In particular `m = m`.

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
          CYP-KO 20
          CYP-KO 21
          CYP-OK 22
          CYP-OK 23
          CYP-OK 24
          CYP-OK 25
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
          File "./cyp_check.v", line 158, characters 127-154:
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
          CYP-OK 8
          CYP-KO 20
          CYP-KO 21
          CYP-OK 22
          CYP-OK 23
          CYP-OK 24
          CYP-OK 25
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
          File "./cyp_check.v", line 158, characters 127-152:
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
    - ✅ We have proved `0 + m = m -> Basics.flip Basics.impl (0 + m = m) (m = m)`.
      - ▫️ Assume `0 + m = m` (lemma).
        - ✅ In particular `Morphisms.ProperProxy eq m`.
          - ❌ Using eq_proper_proxy we get `forall (A : Type) (x : A), Morphisms.ProperProxy eq x` .*by exact @eq_proper_proxy*

            <details><summary>not proved</summary>

            ```
            1 goal
              
              n, m : nat
              H : forall x y : nat, x = y -> x + m = m + x <-> y + m = m + y
              H0 : m + 0 = m
              H1 : 0 + m = m
              H2 : m = m
              H3 : 0 + m = m
              A : Type
              x : A
              ============================
              Morphisms.ProperProxy eq x
            
            File "./cyp_ko_78.v", line 4, characters 0-108:
            Error: No applicable tactic.
            ```

            </details>
        - ✅ In particular `m = m -> Basics.flip Basics.impl (0 + m = m) (m = m)`.
          - ✅ By lemma we have `0 + m = m`.
          - ❌ In particular `0 + m = m -> Morphisms.respectful eq (Basics.flip Basics.impl) (eq (0 + m)) (eq m)`.

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
                CYP-KO 20
                CYP-KO 21
                CYP-OK 22
                CYP-OK 23
                CYP-OK 24
                CYP-OK 25
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
                CYP-KO 78
                CYP-OK 79
                CYP-OK 80
                File "./cyp_check.v", line 170, characters 206-233:
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
                CYP-OK 8
                CYP-KO 20
                CYP-KO 21
                CYP-OK 22
                CYP-OK 23
                CYP-OK 24
                CYP-OK 25
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
                CYP-KO 78
                CYP-OK 79
                CYP-OK 80
                File "./cyp_check.v", line 170, characters 206-232:
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
          - ✅ We deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (eq (0 + m)) (eq m)`.
        - ✅ We deduce `Basics.flip Basics.impl (0 + m = m) (m = m)`.
  - ✅ We have proved `m + 0 = m -> Basics.flip Basics.impl (0 + m = m + 0) (0 + m = m)`.
    - ▫️ Assume `m + 0 = m` (lemma).
      - ✅ By lemma we have `m + 0 = m`.
      - ❌ In particular `m + 0 = m -> Basics.flip Basics.impl (0 + m = m + 0) (0 + m = m)`.

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
            CYP-KO 20
            CYP-KO 21
            CYP-OK 22
            CYP-OK 23
            CYP-OK 24
            CYP-OK 25
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
            CYP-KO 78
            CYP-OK 79
            CYP-OK 80
            CYP-OK 89
            CYP-OK 90
            CYP-OK 91
            CYP-OK 92
            CYP-OK 93
            CYP-OK 94
            File "./cyp_check.v", line 194, characters 159-186:
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
            CYP-OK 8
            CYP-KO 20
            CYP-KO 21
            CYP-OK 22
            CYP-OK 23
            CYP-OK 24
            CYP-OK 25
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
            CYP-KO 78
            CYP-OK 79
            CYP-OK 80
            CYP-OK 89
            CYP-OK 90
            CYP-OK 91
            CYP-OK 92
            CYP-OK 93
            CYP-OK 94
            File "./cyp_check.v", line 194, characters 159-178:
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
      - ✅ We deduce `Basics.flip Basics.impl (0 + m = m + 0) (0 + m = m)`.
- ✅ We have `forall n0 : nat, n0 + m = m + n0 <-> S n0 + m = m + S n0`, since `n0` is arbitrary.
  - ▫️ Let us consider an arbitrary `n0 : nat`.
    - ✅ In particular `m + S n0 = S (m + n0)`.
      - ❌ Using add_succ_r we get `forall n1 m0 : nat, n1 + S m0 = S (n1 + m0)` .*by exact @add_succ_r*

        <details><summary>not proved</summary>

        ```
        1 goal
          
          n, m, n0 : nat
          H : forall x y : nat, x = y -> x + m = m + x <-> y + m = m + y
          H0 : 0 + m = m + 0
          n1, m0 : nat
          ============================
          n1 + S m0 = S (n1 + m0)
        
        File "./cyp_ko_106.v", line 4, characters 0-98:
        Error: No applicable tactic.
        ```

        </details>
    - ✅ We deduce `n0 + m = m + n0 <-> S n0 + m = S (m + n0)`.
      - ✅ In particular `S n0 + m = S (n0 + m)`.
        - ❌ Using add_succ_l we get `forall n1 m0 : nat, S n1 + m0 = S (n1 + m0)` .*by exact @add_succ_l*

          <details><summary>not proved</summary>

          ```
          1 goal
            
            n, m, n0 : nat
            H : forall x y : nat, x = y -> x + m = m + x <-> y + m = m + y
            H0 : 0 + m = m + 0
            H1 : m + S n0 = S (m + n0)
            n1, m0 : nat
            ============================
            S n1 + m0 = S (n1 + m0)
          
          File "./cyp_ko_108.v", line 4, characters 0-98:
          Error: No applicable tactic.
          ```

          </details>
      - ✅ We deduce `n0 + m = m + n0 <-> S (n0 + m) = S (m + n0)`.
        - ✅ In particular `S (n0 + m) = S (m + n0) <-> n0 + m = m + n0`.
          - ❌ Using succ_inj_wd we get `forall n1 n2 : nat, S n1 = S n2 <-> n1 = n2` .*by exact @succ_inj_wd*

            <details><summary>not proved</summary>

            ```
            1 goal
              
              n, m, n0 : nat
              H : forall x y : nat, x = y -> x + m = m + x <-> y + m = m + y
              H0 : 0 + m = m + 0
              H1 : m + S n0 = S (m + n0)
              H2 : S n0 + m = S (n0 + m)
              n1, n2 : nat
              ============================
              S n1 = S n2 <-> n1 = n2
            
            File "./cyp_ko_110.v", line 4, characters 0-100:
            Error: No applicable tactic.
            ```

            </details>
        - ✅ In particular `n0 + m = m + n0 <-> n0 + m = m + n0`.
          - ❌ Using iff_Reflexive we get `RelationClasses.Reflexive iff` .*by exact @iff_Reflexive*

            <details><summary>not proved</summary>

            ```
            1 goal
              
              n, m, n0 : nat
              H : forall x y : nat, x = y -> x + m = m + x <-> y + m = m + y
              H0 : 0 + m = m + 0
              H1 : m + S n0 = S (m + n0)
              H2 : S n0 + m = S (n0 + m)
              H3 : S (n0 + m) = S (m + n0) <-> n0 + m = m + n0
              ============================
              RelationClasses.Reflexive iff
            
            File "./cyp_ko_112.v", line 4, characters 0-104:
            Error: No applicable tactic.
            ```

            </details>
          - ✅ In particular `RelationClasses.Reflexive iff -> forall x : Prop, x <-> x`.
            - ❌ Using reflexivity we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x : A, R x x` .*by exact @reflexivity*

              <details><summary>not proved</summary>

              ```
              1 goal
                
                n, m, n0 : nat
                H : forall x y : nat, x = y -> x + m = m + x <-> y + m = m + y
                H0 : 0 + m = m + 0
                H1 : m + S n0 = S (m + n0)
                H2 : S n0 + m = S (n0 + m)
                H3 : S (n0 + m) = S (m + n0) <-> n0 + m = m + n0
                H4 : RelationClasses.Reflexive iff
                A : Type
                R : Relation_Definitions.relation A
                H5 : RelationClasses.Reflexive R
                x : A
                ============================
                R x x
              
              File "./cyp_ko_113.v", line 4, characters 0-100:
              Error: No applicable tactic.
              ```

              </details>
          - ✅ We deduce `forall x : Prop, x <-> x`.
        - ✅ We have proved `S (n0 + m) = S (m + n0) <-> n0 + m = m + n0 -> Basics.flip Basics.impl (n0 + m = m + n0 <-> S (n0 + m) = S (m + n0)) (n0 + m = m + n0 <-> n0 + m = m + n0)`.
          - ▫️ Assume `S (n0 + m) = S (m + n0) <-> n0 + m = m + n0` (lemma).
            - ✅ By lemma we have `S (n0 + m) = S (m + n0) <-> n0 + m = m + n0`.
            - ✅ In particular `S (n0 + m) = S (m + n0) <-> n0 + m = m + n0 -> Basics.flip Basics.impl (n0 + m = m + n0 <-> S (n0 + m) = S (m + n0)) (n0 + m = m + n0 <-> n0 + m = m + n0)`.
              - ✅ We deduce `RelationClasses.PER iff`.
                - ❌ Using iff_equivalence we get `RelationClasses.Equivalence iff` .*by exact @iff_equivalence*

                  <details><summary>not proved</summary>

                  ```
                  1 goal
                    
                    n, m, n0 : nat
                    H : forall x y : nat, x = y -> x + m = m + x <-> y + m = m + y
                    H0 : 0 + m = m + 0
                    H1 : m + S n0 = S (m + n0)
                    H2 : S n0 + m = S (n0 + m)
                    H3 : S (n0 + m) = S (m + n0) <-> n0 + m = m + n0
                    H4 : n0 + m = m + n0 <-> n0 + m = m + n0
                    H5, H6 : S (n0 + m) = S (m + n0) <-> n0 + m = m + n0
                    ============================
                    RelationClasses.Equivalence iff
                  
                  File "./cyp_ko_118.v", line 4, characters 0-108:
                  Error: No applicable tactic.
                  ```

                  </details>
                - ✅ In particular `RelationClasses.Equivalence iff -> RelationClasses.PER iff`.
                  - ❌ Using Equivalence_PER we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R` .*by exact @Equivalence_PER*

                    <details><summary>not proved</summary>

                    ```
                    1 goal
                      
                      n, m, n0 : nat
                      H : forall x y : nat, x = y -> x + m = m + x <-> y + m = m + y
                      H0 : 0 + m = m + 0
                      H1 : m + S n0 = S (m + n0)
                      H2 : S n0 + m = S (n0 + m)
                      H3 : S (n0 + m) = S (m + n0) <-> n0 + m = m + n0
                      H4 : n0 + m = m + n0 <-> n0 + m = m + n0
                      H5, H6 : S (n0 + m) = S (m + n0) <-> n0 + m = m + n0
                      H7 : RelationClasses.Equivalence iff
                      A : Type
                      R : Relation_Definitions.relation A
                      H8 : RelationClasses.Equivalence R
                      ============================
                      RelationClasses.PER R
                    
                    File "./cyp_ko_119.v", line 4, characters 0-108:
                    Error: No applicable tactic.
                    ```

                    </details>
              - ✅ In particular `RelationClasses.PER iff -> forall x : Prop, Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (iff x)`.
                - ❌ Using trans_sym_co_inv_impl_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> forall x : A, Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)` .*by exact @trans_sym_co_inv_impl_morphism*

                  <details><summary>not proved</summary>

                  ```
                  1 goal
                    
                    n, m, n0 : nat
                    H : forall x y : nat, x = y -> x + m = m + x <-> y + m = m + y
                    H0 : 0 + m = m + 0
                    H1 : m + S n0 = S (m + n0)
                    H2 : S n0 + m = S (n0 + m)
                    H3 : S (n0 + m) = S (m + n0) <-> n0 + m = m + n0
                    H4 : n0 + m = m + n0 <-> n0 + m = m + n0
                    H5, H6 : S (n0 + m) = S (m + n0) <-> n0 + m = m + n0
                    H7 : RelationClasses.PER iff
                    A : Type
                    R : Relation_Definitions.relation A
                    H8 : RelationClasses.PER R
                    x : A
                    ============================
                    Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)
                  
                  File "./cyp_ko_122.v", line 4, characters 0-138:
                  Error: No applicable tactic.
                  ```

                  </details>
              - ✅ We deduce `forall x : Prop, Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (iff x)`.
            - ✅ We deduce `Basics.flip Basics.impl (n0 + m = m + n0 <-> S (n0 + m) = S (m + n0)) (n0 + m = m + n0 <-> n0 + m = m + n0)`.
      - ✅ We have proved `S n0 + m = S (n0 + m) -> Basics.flip Basics.impl (n0 + m = m + n0 <-> S n0 + m = S (m + n0)) (n0 + m = m + n0 <-> S (n0 + m) = S (m + n0))`.
        - ▫️ Assume `S n0 + m = S (n0 + m)` (lemma).
          - ✅ We deduce `S n0 + m = S (m + n0) <-> S (n0 + m) = S (m + n0)`.
            - ❌ In particular `Morphisms.ProperProxy eq (S (m + n0))`.

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
                    CYP-KO 20
                    CYP-KO 21
                    CYP-OK 22
                    CYP-OK 23
                    CYP-OK 24
                    CYP-OK 25
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
                    CYP-KO 78
                    CYP-OK 79
                    CYP-OK 80
                    CYP-OK 89
                    CYP-OK 90
                    CYP-OK 91
                    CYP-OK 92
                    CYP-OK 93
                    CYP-OK 94
                    CYP-OK 103
                    CYP-OK 104
                    CYP-OK 105
                    CYP-KO 106
                    CYP-OK 107
                    CYP-KO 108
                    CYP-OK 109
                    CYP-KO 110
                    CYP-OK 111
                    CYP-KO 112
                    CYP-KO 113
                    CYP-OK 114
                    CYP-OK 115
                    CYP-OK 116
                    CYP-OK 117
                    CYP-KO 118
                    CYP-KO 119
                    CYP-OK 120
                    CYP-OK 121
                    CYP-KO 122
                    CYP-OK 123
                    CYP-OK 124
                    CYP-OK 125
                    CYP-OK 126
                    CYP-OK 127
                    CYP-OK 128
                    File "./cyp_check.v", line 298, characters 261-288:
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
                    CYP-OK 8
                    CYP-KO 20
                    CYP-KO 21
                    CYP-OK 22
                    CYP-OK 23
                    CYP-OK 24
                    CYP-OK 25
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
                    CYP-KO 78
                    CYP-OK 79
                    CYP-OK 80
                    CYP-OK 89
                    CYP-OK 90
                    CYP-OK 91
                    CYP-OK 92
                    CYP-OK 93
                    CYP-OK 94
                    CYP-OK 103
                    CYP-OK 104
                    CYP-OK 105
                    CYP-KO 106
                    CYP-OK 107
                    CYP-KO 108
                    CYP-OK 109
                    CYP-KO 110
                    CYP-OK 111
                    CYP-KO 112
                    CYP-KO 113
                    CYP-OK 114
                    CYP-OK 115
                    CYP-OK 116
                    CYP-OK 117
                    CYP-KO 118
                    CYP-KO 119
                    CYP-OK 120
                    CYP-OK 121
                    CYP-KO 122
                    CYP-OK 123
                    CYP-OK 124
                    CYP-OK 125
                    CYP-OK 126
                    CYP-OK 127
                    CYP-OK 128
                    File "./cyp_check.v", line 298, characters 261-286:
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
                  CYP-OK 8
                  CYP-KO 20
                  CYP-KO 21
                  CYP-OK 22
                  CYP-OK 23
                  CYP-OK 24
                  CYP-OK 25
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
                  CYP-KO 78
                  CYP-OK 79
                  CYP-OK 80
                  CYP-OK 89
                  CYP-OK 90
                  CYP-OK 91
                  CYP-OK 92
                  CYP-OK 93
                  CYP-OK 94
                  CYP-OK 103
                  CYP-OK 104
                  CYP-OK 105
                  CYP-KO 106
                  CYP-OK 107
                  CYP-KO 108
                  CYP-OK 109
                  CYP-KO 110
                  CYP-OK 111
                  CYP-KO 112
                  CYP-KO 113
                  CYP-OK 114
                  CYP-OK 115
                  CYP-OK 116
                  CYP-OK 117
                  CYP-KO 118
                  CYP-KO 119
                  CYP-OK 120
                  CYP-OK 121
                  CYP-KO 122
                  CYP-OK 123
                  CYP-OK 124
                  CYP-OK 125
                  CYP-OK 126
                  CYP-OK 127
                  CYP-OK 128
                  File "./cyp_check.v", line 298, characters 261-285:
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
            - ✅ In particular `S (m + n0) = S (m + n0) -> S n0 + m = S (m + n0) <-> S (n0 + m) = S (m + n0)`.
              - ✅ By lemma we have `S n0 + m = S (n0 + m)`.
              - ❌ In particular `S n0 + m = S (n0 + m) -> Morphisms.respectful eq iff (eq (S n0 + m)) (eq (S (n0 + m)))`.

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
                    CYP-KO 20
                    CYP-KO 21
                    CYP-OK 22
                    CYP-OK 23
                    CYP-OK 24
                    CYP-OK 25
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
                    CYP-KO 78
                    CYP-OK 79
                    CYP-OK 80
                    CYP-OK 89
                    CYP-OK 90
                    CYP-OK 91
                    CYP-OK 92
                    CYP-OK 93
                    CYP-OK 94
                    CYP-OK 103
                    CYP-OK 104
                    CYP-OK 105
                    CYP-KO 106
                    CYP-OK 107
                    CYP-KO 108
                    CYP-OK 109
                    CYP-KO 110
                    CYP-OK 111
                    CYP-KO 112
                    CYP-KO 113
                    CYP-OK 114
                    CYP-OK 115
                    CYP-OK 116
                    CYP-OK 117
                    CYP-KO 118
                    CYP-KO 119
                    CYP-OK 120
                    CYP-OK 121
                    CYP-KO 122
                    CYP-OK 123
                    CYP-OK 124
                    CYP-OK 125
                    CYP-OK 126
                    CYP-OK 127
                    CYP-OK 128
                    CYP-OK 140
                    File "./cyp_check.v", line 302, characters 335-362:
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
                    CYP-OK 8
                    CYP-KO 20
                    CYP-KO 21
                    CYP-OK 22
                    CYP-OK 23
                    CYP-OK 24
                    CYP-OK 25
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
                    CYP-KO 78
                    CYP-OK 79
                    CYP-OK 80
                    CYP-OK 89
                    CYP-OK 90
                    CYP-OK 91
                    CYP-OK 92
                    CYP-OK 93
                    CYP-OK 94
                    CYP-OK 103
                    CYP-OK 104
                    CYP-OK 105
                    CYP-KO 106
                    CYP-OK 107
                    CYP-KO 108
                    CYP-OK 109
                    CYP-KO 110
                    CYP-OK 111
                    CYP-KO 112
                    CYP-KO 113
                    CYP-OK 114
                    CYP-OK 115
                    CYP-OK 116
                    CYP-OK 117
                    CYP-KO 118
                    CYP-KO 119
                    CYP-OK 120
                    CYP-OK 121
                    CYP-KO 122
                    CYP-OK 123
                    CYP-OK 124
                    CYP-OK 125
                    CYP-OK 126
                    CYP-OK 127
                    CYP-OK 128
                    CYP-OK 140
                    File "./cyp_check.v", line 302, characters 335-354:
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
              - ✅ We deduce `Morphisms.respectful eq iff (eq (S n0 + m)) (eq (S (n0 + m)))`.
          - ✅ In particular `S n0 + m = S (m + n0) <-> S (n0 + m) = S (m + n0) -> Basics.flip Basics.impl (n0 + m = m + n0 <-> S n0 + m = S (m + n0)) (n0 + m = m + n0 <-> S (n0 + m) = S (m + n0))`.
            - ✅ We deduce `RelationClasses.PER iff`.
              - ❌ Using iff_equivalence we get `RelationClasses.Equivalence iff` .*by exact @iff_equivalence*

                <details><summary>not proved</summary>

                ```
                1 goal
                  
                  n, m, n0 : nat
                  H : forall x y : nat, x = y -> x + m = m + x <-> y + m = m + y
                  H0 : 0 + m = m + 0
                  H1 : m + S n0 = S (m + n0)
                  H2 : S n0 + m = S (n0 + m)
                  H3 : n0 + m = m + n0 <-> S (n0 + m) = S (m + n0)
                  H4 : S n0 + m = S (n0 + m)
                  H5 : S n0 + m = S (m + n0) <-> S (n0 + m) = S (m + n0)
                  ============================
                  RelationClasses.Equivalence iff
                
                File "./cyp_ko_152.v", line 4, characters 0-108:
                Error: No applicable tactic.
                ```

                </details>
              - ✅ In particular `RelationClasses.Equivalence iff -> RelationClasses.PER iff`.
                - ❌ Using Equivalence_PER we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R` .*by exact @Equivalence_PER*

                  <details><summary>not proved</summary>

                  ```
                  1 goal
                    
                    n, m, n0 : nat
                    H : forall x y : nat, x = y -> x + m = m + x <-> y + m = m + y
                    H0 : 0 + m = m + 0
                    H1 : m + S n0 = S (m + n0)
                    H2 : S n0 + m = S (n0 + m)
                    H3 : n0 + m = m + n0 <-> S (n0 + m) = S (m + n0)
                    H4 : S n0 + m = S (n0 + m)
                    H5 : S n0 + m = S (m + n0) <-> S (n0 + m) = S (m + n0)
                    H6 : RelationClasses.Equivalence iff
                    A : Type
                    R : Relation_Definitions.relation A
                    H7 : RelationClasses.Equivalence R
                    ============================
                    RelationClasses.PER R
                  
                  File "./cyp_ko_153.v", line 4, characters 0-108:
                  Error: No applicable tactic.
                  ```

                  </details>
            - ✅ In particular `RelationClasses.PER iff -> forall x : Prop, Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (iff x)`.
              - ❌ Using trans_sym_co_inv_impl_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> forall x : A, Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)` .*by exact @trans_sym_co_inv_impl_morphism*

                <details><summary>not proved</summary>

                ```
                1 goal
                  
                  n, m, n0 : nat
                  H : forall x y : nat, x = y -> x + m = m + x <-> y + m = m + y
                  H0 : 0 + m = m + 0
                  H1 : m + S n0 = S (m + n0)
                  H2 : S n0 + m = S (n0 + m)
                  H3 : n0 + m = m + n0 <-> S (n0 + m) = S (m + n0)
                  H4 : S n0 + m = S (n0 + m)
                  H5 : S n0 + m = S (m + n0) <-> S (n0 + m) = S (m + n0)
                  H6 : RelationClasses.PER iff
                  A : Type
                  R : Relation_Definitions.relation A
                  H7 : RelationClasses.PER R
                  x : A
                  ============================
                  Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)
                
                File "./cyp_ko_156.v", line 4, characters 0-138:
                Error: No applicable tactic.
                ```

                </details>
            - ✅ We deduce `forall x : Prop, Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (iff x)`.
          - ✅ We deduce `Basics.flip Basics.impl (n0 + m = m + n0 <-> S n0 + m = S (m + n0)) (n0 + m = m + n0 <-> S (n0 + m) = S (m + n0))`.
    - ✅ We have proved `m + S n0 = S (m + n0) -> Basics.flip Basics.impl (n0 + m = m + n0 <-> S n0 + m = m + S n0) (n0 + m = m + n0 <-> S n0 + m = S (m + n0))`.
      - ▫️ Assume `m + S n0 = S (m + n0)` (lemma).
        - ✅ We deduce `S n0 + m = m + S n0 <-> S n0 + m = S (m + n0)`.
          - ✅ By lemma we have `m + S n0 = S (m + n0)`.
          - ❌ In particular `m + S n0 = S (m + n0) -> S n0 + m = m + S n0 <-> S n0 + m = S (m + n0)`.

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
                CYP-KO 20
                CYP-KO 21
                CYP-OK 22
                CYP-OK 23
                CYP-OK 24
                CYP-OK 25
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
                CYP-KO 78
                CYP-OK 79
                CYP-OK 80
                CYP-OK 89
                CYP-OK 90
                CYP-OK 91
                CYP-OK 92
                CYP-OK 93
                CYP-OK 94
                CYP-OK 103
                CYP-OK 104
                CYP-OK 105
                CYP-KO 106
                CYP-OK 107
                CYP-KO 108
                CYP-OK 109
                CYP-KO 110
                CYP-OK 111
                CYP-KO 112
                CYP-KO 113
                CYP-OK 114
                CYP-OK 115
                CYP-OK 116
                CYP-OK 117
                CYP-KO 118
                CYP-KO 119
                CYP-OK 120
                CYP-OK 121
                CYP-KO 122
                CYP-OK 123
                CYP-OK 124
                CYP-OK 125
                CYP-OK 126
                CYP-OK 127
                CYP-OK 128
                CYP-OK 140
                CYP-OK 149
                CYP-OK 150
                CYP-OK 151
                CYP-KO 152
                CYP-KO 153
                CYP-OK 154
                CYP-OK 155
                CYP-KO 156
                CYP-OK 157
                CYP-OK 158
                CYP-OK 159
                CYP-OK 160
                CYP-OK 161
                CYP-OK 162
                CYP-OK 163
                File "./cyp_check.v", line 362, characters 259-286:
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
                CYP-OK 8
                CYP-KO 20
                CYP-KO 21
                CYP-OK 22
                CYP-OK 23
                CYP-OK 24
                CYP-OK 25
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
                CYP-KO 78
                CYP-OK 79
                CYP-OK 80
                CYP-OK 89
                CYP-OK 90
                CYP-OK 91
                CYP-OK 92
                CYP-OK 93
                CYP-OK 94
                CYP-OK 103
                CYP-OK 104
                CYP-OK 105
                CYP-KO 106
                CYP-OK 107
                CYP-KO 108
                CYP-OK 109
                CYP-KO 110
                CYP-OK 111
                CYP-KO 112
                CYP-KO 113
                CYP-OK 114
                CYP-OK 115
                CYP-OK 116
                CYP-OK 117
                CYP-KO 118
                CYP-KO 119
                CYP-OK 120
                CYP-OK 121
                CYP-KO 122
                CYP-OK 123
                CYP-OK 124
                CYP-OK 125
                CYP-OK 126
                CYP-OK 127
                CYP-OK 128
                CYP-OK 140
                CYP-OK 149
                CYP-OK 150
                CYP-OK 151
                CYP-KO 152
                CYP-KO 153
                CYP-OK 154
                CYP-OK 155
                CYP-KO 156
                CYP-OK 157
                CYP-OK 158
                CYP-OK 159
                CYP-OK 160
                CYP-OK 161
                CYP-OK 162
                CYP-OK 163
                File "./cyp_check.v", line 362, characters 259-278:
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
        - ✅ In particular `S n0 + m = m + S n0 <-> S n0 + m = S (m + n0) -> Basics.flip Basics.impl (n0 + m = m + n0 <-> S n0 + m = m + S n0) (n0 + m = m + n0 <-> S n0 + m = S (m + n0))`.
          - ✅ We deduce `RelationClasses.PER iff`.
            - ❌ Using iff_equivalence we get `RelationClasses.Equivalence iff` .*by exact @iff_equivalence*

              <details><summary>not proved</summary>

              ```
              1 goal
                
                n, m, n0 : nat
                H : forall x y : nat, x = y -> x + m = m + x <-> y + m = m + y
                H0 : 0 + m = m + 0
                H1 : m + S n0 = S (m + n0)
                H2 : n0 + m = m + n0 <-> S n0 + m = S (m + n0)
                H3 : m + S n0 = S (m + n0)
                H4 : S n0 + m = m + S n0 <-> S n0 + m = S (m + n0)
                ============================
                RelationClasses.Equivalence iff
              
              File "./cyp_ko_173.v", line 4, characters 0-108:
              Error: No applicable tactic.
              ```

              </details>
            - ✅ In particular `RelationClasses.Equivalence iff -> RelationClasses.PER iff`.
              - ❌ Using Equivalence_PER we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R` .*by exact @Equivalence_PER*

                <details><summary>not proved</summary>

                ```
                1 goal
                  
                  n, m, n0 : nat
                  H : forall x y : nat, x = y -> x + m = m + x <-> y + m = m + y
                  H0 : 0 + m = m + 0
                  H1 : m + S n0 = S (m + n0)
                  H2 : n0 + m = m + n0 <-> S n0 + m = S (m + n0)
                  H3 : m + S n0 = S (m + n0)
                  H4 : S n0 + m = m + S n0 <-> S n0 + m = S (m + n0)
                  H5 : RelationClasses.Equivalence iff
                  A : Type
                  R : Relation_Definitions.relation A
                  H6 : RelationClasses.Equivalence R
                  ============================
                  RelationClasses.PER R
                
                File "./cyp_ko_174.v", line 4, characters 0-108:
                Error: No applicable tactic.
                ```

                </details>
          - ✅ In particular `RelationClasses.PER iff -> forall x : Prop, Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (iff x)`.
            - ❌ Using trans_sym_co_inv_impl_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> forall x : A, Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)` .*by exact @trans_sym_co_inv_impl_morphism*

              <details><summary>not proved</summary>

              ```
              1 goal
                
                n, m, n0 : nat
                H : forall x y : nat, x = y -> x + m = m + x <-> y + m = m + y
                H0 : 0 + m = m + 0
                H1 : m + S n0 = S (m + n0)
                H2 : n0 + m = m + n0 <-> S n0 + m = S (m + n0)
                H3 : m + S n0 = S (m + n0)
                H4 : S n0 + m = m + S n0 <-> S n0 + m = S (m + n0)
                H5 : RelationClasses.PER iff
                A : Type
                R : Relation_Definitions.relation A
                H6 : RelationClasses.PER R
                x : A
                ============================
                Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)
              
              File "./cyp_ko_177.v", line 4, characters 0-138:
              Error: No applicable tactic.
              ```

              </details>
          - ✅ We deduce `forall x : Prop, Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (iff x)`.
        - ✅ We deduce `Basics.flip Basics.impl (n0 + m = m + n0 <-> S n0 + m = m + S n0) (n0 + m = m + n0 <-> S n0 + m = S (m + n0))`.
    - ✅ We deduce `n0 + m = m + n0 <-> S n0 + m = m + S n0`.
- ✅ In particular `Morphisms.Proper (Morphisms.respectful eq iff) (fun t : nat => t + m = m + t) -> 0 + m = m + 0 -> (forall n0 : nat, n0 + m = m + n0 <-> S n0 + m = m + S n0) -> forall n0 : nat, n0 + m = m + n0`.
  - ❌ Using bi_induction we get `forall A : nat -> Prop, Morphisms.Proper (Morphisms.respectful eq iff) A -> A 0 -> (forall n0 : nat, A n0 <-> A (S n0)) -> forall n0 : nat, A n0` .*by exact @bi_induction*

    <details><summary>not proved</summary>

    ```
    1 goal
      
      n, m : nat
      H : forall x y : nat, x = y -> x + m = m + x <-> y + m = m + y
      H0 : 0 + m = m + 0
      H1 : forall n0 : nat, n0 + m = m + n0 <-> S n0 + m = m + S n0
      A : nat -> Prop
      H2 : Morphisms.Proper (Morphisms.respectful eq iff) A
      H3 : A 0
      H4 : forall n0 : nat, A n0 <-> A (S n0)
      n0 : nat
      ============================
      A n0
    
    File "./cyp_ko_185.v", line 4, characters 0-102:
    Error: No applicable tactic.
    ```

    </details>
- ✅ We deduce `forall n0 : nat, n0 + m = m + n0`.
- ✅ In particular `n + m = m + n`.

