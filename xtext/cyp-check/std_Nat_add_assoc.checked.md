<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# Nat.add_assoc

✅ Let `n m p : nat`. We prove `n + (m + p) = n + m + p`.

- ✅ Thus we have `forall x y : nat, x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p`.
  - ▫️ Let us choose arbitrarily `x : nat`, `y : nat`.
    - ▫️ Assume `x = y` (H).
      - ✅ In particular `Morphisms.ProperProxy eq (y + (m + p) = y + m + p)`.
        - ❌ Using eq_proper_proxy we get `forall (A : Type) (x0 : A), Morphisms.ProperProxy eq x0` .*by exact @eq_proper_proxy*

          <details><summary>not proved</summary>

          ```
          1 goal
            
            n, m, p, x, y : nat
            H : x = y
            A : Type
            x0 : A
            ============================
            Morphisms.ProperProxy eq x0
          
          File "./cyp_ko_1.v", line 4, characters 0-108:
          Error: No applicable tactic.
          ```

          </details>
      - ✅ In particular `y + (m + p) = y + m + p <-> y + (m + p) = y + m + p`.
        - ❌ Using iff_Reflexive we get `RelationClasses.Reflexive iff` .*by exact @iff_Reflexive*

          <details><summary>not proved</summary>

          ```
          1 goal
            
            n, m, p, x, y : nat
            H : x = y
            H0 : Morphisms.ProperProxy eq (y + (m + p) = y + m + p)
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
              
              n, m, p, x, y : nat
              H : x = y
              H0 : Morphisms.ProperProxy eq (y + (m + p) = y + m + p)
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
      - ✅ In particular `(y + (m + p) = y + m + p) = (y + (m + p) = y + m + p) -> Basics.flip Basics.impl (x + (m + p) = x + m + p <-> y + (m + p) = y + m + p) (y + (m + p) = y + m + p <-> y + (m + p) = y + m + p)`.
        - ✅ We deduce `x + (m + p) = x + m + p <-> y + (m + p) = y + m + p`.
          - ✅ We deduce `x + m + p = y + m + p`.
            - ❌ In particular `Morphisms.ProperProxy eq p`.

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
                    File "./cyp_check.v", line 30, characters 177-204:
                    Error: Cannot infer the implicit parameter A of RelationClasses.Equivalence
                    whose type is "Type" in environment:
                    n, m, p, x, y : nat
                    
                    
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
                    File "./cyp_check.v", line 30, characters 177-202:
                    Error: Cannot infer the implicit parameter A of RelationClasses.Reflexive
                    whose type is "Type" in environment:
                    n, m, p, x, y : nat
                    
                    
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
                  File "./cyp_check.v", line 30, characters 177-201:
                  Error: Cannot infer the implicit parameter A of Morphisms.ReflexiveProxy
                  whose type is "Type" in environment:
                  n, m, p, x, y : nat
                  
                  
                  ```

                  </details>
              - ❌ We deduce `forall x0 : nat, Morphisms.ProperProxy eq x0`.

                <details><summary>Rocq error</summary>

                ```
                This step does not type-check because an earlier step does not: see the first Rocq error above.
                ```

                </details>
            - ✅ In particular `p = p -> x + m + p = y + m + p`.
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
                        This step does not type-check because an earlier step does not: see the first Rocq error above.
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
                        This step does not type-check because an earlier step does not: see the first Rocq error above.
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
                      This step does not type-check because an earlier step does not: see the first Rocq error above.
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
                        
                        n, m, p, x, y : nat
                        H : x = y
                        H0 : Morphisms.ProperProxy eq (y + (m + p) = y + m + p)
                        H1 : y + (m + p) = y + m + p <-> y + (m + p) = y + m + p
                        H2 : Morphisms.ProperProxy eq p
                        H3 : Morphisms.ProperProxy eq m
                        H4 : x = y
                        ============================
                        Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq))
                          Init.Nat.add
                      
                      File "./cyp_ko_31.v", line 4, characters 0-90:
                      Error: No applicable tactic.
                      ```

                      </details>
                  - ✅ We deduce `Morphisms.respectful eq eq (Init.Nat.add x) (Init.Nat.add y)`.
              - ✅ In particular `x + m = y + m -> Morphisms.respectful eq eq (Init.Nat.add (x + m)) (Init.Nat.add (y + m))`.
                - ❌ Using add_wd we get `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Init.Nat.add` .*by exact @add_wd*

                  <details><summary>not proved</summary>

                  ```
                  1 goal
                    
                    n, m, p, x, y : nat
                    H : x = y
                    H0 : Morphisms.ProperProxy eq (y + (m + p) = y + m + p)
                    H1 : y + (m + p) = y + m + p <-> y + (m + p) = y + m + p
                    H2 : Morphisms.ProperProxy eq p
                    H3 : x + m = y + m
                    ============================
                    Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq))
                      Init.Nat.add
                  
                  File "./cyp_ko_36.v", line 4, characters 0-90:
                  Error: No applicable tactic.
                  ```

                  </details>
              - ✅ We deduce `Morphisms.respectful eq eq (Init.Nat.add (x + m)) (Init.Nat.add (y + m))`.
          - ✅ In particular `x + m + p = y + m + p -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p`.
            - ✅ We deduce `x + (m + p) = y + (m + p)`.
              - ❌ In particular `Morphisms.ProperProxy eq (m + p)`.

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
                      CYP-OK 30
                      CYP-KO 31
                      CYP-OK 32
                      CYP-OK 33
                      CYP-OK 34
                      CYP-OK 35
                      CYP-KO 36
                      CYP-OK 37
                      CYP-OK 38
                      CYP-OK 39
                      CYP-OK 40
                      File "./cyp_check.v", line 74, characters 206-233:
                      Error: Cannot infer the implicit parameter A of RelationClasses.Equivalence
                      whose type is "Type" in environment:
                      n, m, p, x, y : nat
                      
                      
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
                      CYP-OK 30
                      CYP-KO 31
                      CYP-OK 32
                      CYP-OK 33
                      CYP-OK 34
                      CYP-OK 35
                      CYP-KO 36
                      CYP-OK 37
                      CYP-OK 38
                      CYP-OK 39
                      CYP-OK 40
                      File "./cyp_check.v", line 74, characters 206-231:
                      Error: Cannot infer the implicit parameter A of RelationClasses.Reflexive
                      whose type is "Type" in environment:
                      n, m, p, x, y : nat
                      
                      
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
                    CYP-OK 30
                    CYP-KO 31
                    CYP-OK 32
                    CYP-OK 33
                    CYP-OK 34
                    CYP-OK 35
                    CYP-KO 36
                    CYP-OK 37
                    CYP-OK 38
                    CYP-OK 39
                    CYP-OK 40
                    File "./cyp_check.v", line 74, characters 206-230:
                    Error: Cannot infer the implicit parameter A of Morphisms.ReflexiveProxy
                    whose type is "Type" in environment:
                    n, m, p, x, y : nat
                    
                    
                    ```

                    </details>
                - ❌ We deduce `forall x0 : nat, Morphisms.ProperProxy eq x0`.

                  <details><summary>Rocq error</summary>

                  ```
                  This step does not type-check because an earlier step does not: see the first Rocq error above.
                  ```

                  </details>
              - ✅ In particular `m + p = m + p -> x + (m + p) = y + (m + p)`.
                - ✅ By H we have `x = y`.
                - ✅ In particular `x = y -> Morphisms.respectful eq eq (Init.Nat.add x) (Init.Nat.add y)`.
                  - ❌ Using add_wd we get `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Init.Nat.add` .*by exact @add_wd*

                    <details><summary>not proved</summary>

                    ```
                    1 goal
                      
                      n, m, p, x, y : nat
                      H : x = y
                      H0 : Morphisms.ProperProxy eq (y + (m + p) = y + m + p)
                      H1 : y + (m + p) = y + m + p <-> y + (m + p) = y + m + p
                      H2 : x + m + p = y + m + p
                      H3 : Morphisms.ProperProxy eq (m + p)
                      H4 : x = y
                      ============================
                      Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq))
                        Init.Nat.add
                    
                    File "./cyp_ko_53.v", line 4, characters 0-90:
                    Error: No applicable tactic.
                    ```

                    </details>
                - ✅ We deduce `Morphisms.respectful eq eq (Init.Nat.add x) (Init.Nat.add y)`.
            - ❌ In particular `x + (m + p) = y + (m + p) -> Morphisms.respectful eq iff (eq (x + (m + p))) (eq (y + (m + p)))`.

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
                  CYP-OK 30
                  CYP-KO 31
                  CYP-OK 32
                  CYP-OK 33
                  CYP-OK 34
                  CYP-OK 35
                  CYP-KO 36
                  CYP-OK 37
                  CYP-OK 38
                  CYP-OK 39
                  CYP-OK 40
                  CYP-OK 52
                  CYP-KO 53
                  CYP-OK 54
                  CYP-OK 55
                  CYP-OK 56
                  CYP-OK 57
                  File "./cyp_check.v", line 98, characters 239-266:
                  Error: Cannot infer the implicit parameter A of RelationClasses.Equivalence
                  whose type is "Type" in environment:
                  n, m, p, x, y : nat
                  
                  
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
                  CYP-OK 30
                  CYP-KO 31
                  CYP-OK 32
                  CYP-OK 33
                  CYP-OK 34
                  CYP-OK 35
                  CYP-KO 36
                  CYP-OK 37
                  CYP-OK 38
                  CYP-OK 39
                  CYP-OK 40
                  CYP-OK 52
                  CYP-KO 53
                  CYP-OK 54
                  CYP-OK 55
                  CYP-OK 56
                  CYP-OK 57
                  File "./cyp_check.v", line 98, characters 239-258:
                  Error: Cannot infer the implicit parameter A of RelationClasses.PER whose
                  type is "Type" in environment:
                  n, m, p, x, y : nat
                  
                  
                  ```

                  </details>
              - ❌ We deduce `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq iff)) eq`.

                <details><summary>Rocq error</summary>

                ```
                This step does not type-check because an earlier step does not: see the first Rocq error above.
                ```

                </details>
            - ✅ We deduce `Morphisms.respectful eq iff (eq (x + (m + p))) (eq (y + (m + p)))`.
        - ✅ In particular `x + (m + p) = x + m + p <-> y + (m + p) = y + m + p -> Morphisms.respectful eq (Basics.flip Basics.impl) (iff (x + (m + p) = x + m + p)) (iff (y + (m + p) = y + m + p))`.
          - ❌ Using iff_Transitive we get `RelationClasses.Transitive iff` .*by exact @iff_Transitive*

            <details><summary>not proved</summary>

            ```
            1 goal
              
              n, m, p, x, y : nat
              H : x = y
              H0 : Morphisms.ProperProxy eq (y + (m + p) = y + m + p)
              H1 : y + (m + p) = y + m + p <-> y + (m + p) = y + m + p
              H2 : x + (m + p) = x + m + p <-> y + (m + p) = y + m + p
              ============================
              RelationClasses.Transitive iff
            
            File "./cyp_ko_69.v", line 4, characters 0-106:
            Error: No applicable tactic.
            ```

            </details>
          - ✅ In particular `RelationClasses.Transitive iff -> Morphisms.Proper (Morphisms.respectful iff (Morphisms.respectful eq (Basics.flip Basics.impl))) iff`.
            - ❌ Using trans_co_eq_inv_impl_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Transitive R -> Morphisms.Proper (Morphisms.respectful R (Morphisms.respectful eq (Basics.flip Basics.impl))) R` .*by exact @trans_co_eq_inv_impl_morphism*

              <details><summary>not proved</summary>

              ```
              1 goal
                
                n, m, p, x, y : nat
                H : x = y
                H0 : Morphisms.ProperProxy eq (y + (m + p) = y + m + p)
                H1 : y + (m + p) = y + m + p <-> y + (m + p) = y + m + p
                H2 : x + (m + p) = x + m + p <-> y + (m + p) = y + m + p
                H3 : RelationClasses.Transitive iff
                A : Type
                R : Relation_Definitions.relation A
                H4 : RelationClasses.Transitive R
                ============================
                Morphisms.Proper
                  (Morphisms.respectful R
                     (Morphisms.respectful eq (Basics.flip Basics.impl)))
                  R
              
              File "./cyp_ko_70.v", line 4, characters 0-136:
              Error: No applicable tactic.
              ```

              </details>
          - ✅ We deduce `Morphisms.Proper (Morphisms.respectful iff (Morphisms.respectful eq (Basics.flip Basics.impl))) iff`.
        - ✅ We deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (iff (x + (m + p) = x + m + p)) (iff (y + (m + p) = y + m + p))`.
      - ✅ We deduce `x + (m + p) = x + m + p <-> y + (m + p) = y + m + p`.
    - ✅ We have proved `x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p`.
- ✅ We deduce `0 + (m + p) = 0 + m + p`.
  - ✅ In particular `0 + (m + p) = m + p`.
    - ❌ Using add_0_l we get `forall n0 : nat, 0 + n0 = n0` .*by exact @add_0_l*

      <details><summary>not proved</summary>

      ```
      1 goal
        
        n, m, p : nat
        H :
          forall x y : nat,
          x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p
        n0 : nat
        ============================
        0 + n0 = n0
      
      File "./cyp_ko_79.v", line 4, characters 0-92:
      Error: No applicable tactic.
      ```

      </details>
  - ✅ We deduce `m + p = 0 + m + p`.
    - ✅ In particular `0 + m = m`.
      - ❌ Using add_0_l we get `forall n0 : nat, 0 + n0 = n0` .*by exact @add_0_l*

        <details><summary>not proved</summary>

        ```
        1 goal
          
          n, m, p : nat
          H :
            forall x y : nat,
            x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p
          H0 : 0 + (m + p) = m + p
          n0 : nat
          ============================
          0 + n0 = n0
        
        File "./cyp_ko_81.v", line 4, characters 0-92:
        Error: No applicable tactic.
        ```

        </details>
    - ❌ In particular `m + p = m + p`.

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
          CYP-OK 30
          CYP-KO 31
          CYP-OK 32
          CYP-OK 33
          CYP-OK 34
          CYP-OK 35
          CYP-KO 36
          CYP-OK 37
          CYP-OK 38
          CYP-OK 39
          CYP-OK 40
          CYP-OK 52
          CYP-KO 53
          CYP-OK 54
          CYP-OK 55
          CYP-OK 56
          CYP-OK 57
          CYP-OK 66
          CYP-OK 67
          CYP-OK 68
          CYP-KO 69
          CYP-KO 70
          CYP-OK 71
          CYP-OK 72
          CYP-OK 73
          CYP-OK 74
          CYP-OK 75
          CYP-OK 76
          CYP-OK 77
          CYP-OK 78
          CYP-KO 79
          CYP-OK 80
          CYP-KO 81
          CYP-OK 82
          File "./cyp_check.v", line 166, characters 159-186:
          Error: Cannot infer the implicit parameter A of RelationClasses.Equivalence
          whose type is "Type" in environment:
          n, m, p : nat
          
          
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
          CYP-OK 30
          CYP-KO 31
          CYP-OK 32
          CYP-OK 33
          CYP-OK 34
          CYP-OK 35
          CYP-KO 36
          CYP-OK 37
          CYP-OK 38
          CYP-OK 39
          CYP-OK 40
          CYP-OK 52
          CYP-KO 53
          CYP-OK 54
          CYP-OK 55
          CYP-OK 56
          CYP-OK 57
          CYP-OK 66
          CYP-OK 67
          CYP-OK 68
          CYP-KO 69
          CYP-KO 70
          CYP-OK 71
          CYP-OK 72
          CYP-OK 73
          CYP-OK 74
          CYP-OK 75
          CYP-OK 76
          CYP-OK 77
          CYP-OK 78
          CYP-KO 79
          CYP-OK 80
          CYP-KO 81
          CYP-OK 82
          File "./cyp_check.v", line 166, characters 159-184:
          Error: Cannot infer the implicit parameter A of RelationClasses.Reflexive
          whose type is "Type" in environment:
          n, m, p : nat
          
          
          ```

          </details>
      - ❌ We deduce `forall x : nat, x = x`.

        <details><summary>Rocq error</summary>

        ```
        This step does not type-check because an earlier step does not: see the first Rocq error above.
        ```

        </details>
    - ✅ We have proved `0 + m = m -> Basics.flip Basics.impl (m + p = 0 + m + p) (m + p = m + p)`.
      - ▫️ Assume `0 + m = m` (lemma).
        - ✅ We deduce `0 + m + p = m + p`.
          - ❌ In particular `Morphisms.ProperProxy eq p`.

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
                  This step does not type-check because an earlier step does not: see the first Rocq error above.
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
                  This step does not type-check because an earlier step does not: see the first Rocq error above.
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
                CYP-OK 30
                CYP-KO 31
                CYP-OK 32
                CYP-OK 33
                CYP-OK 34
                CYP-OK 35
                CYP-KO 36
                CYP-OK 37
                CYP-OK 38
                CYP-OK 39
                CYP-OK 40
                CYP-OK 52
                CYP-KO 53
                CYP-OK 54
                CYP-OK 55
                CYP-OK 56
                CYP-OK 57
                CYP-OK 66
                CYP-OK 67
                CYP-OK 68
                CYP-KO 69
                CYP-KO 70
                CYP-OK 71
                CYP-OK 72
                CYP-OK 73
                CYP-OK 74
                CYP-OK 75
                CYP-OK 76
                CYP-OK 77
                CYP-OK 78
                CYP-KO 79
                CYP-OK 80
                CYP-KO 81
                CYP-OK 82
                File "./cyp_check.v", line 166, characters 195-219:
                Error: Cannot infer the implicit parameter A of Morphisms.ReflexiveProxy
                whose type is "Type" in environment:
                n, m, p : nat
                
                
                ```

                </details>
            - ❌ We deduce `forall x : nat, Morphisms.ProperProxy eq x`.

              <details><summary>Rocq error</summary>

              ```
              This step does not type-check because an earlier step does not: see the first Rocq error above.
              ```

              </details>
          - ✅ In particular `p = p -> 0 + m + p = m + p`.
            - ✅ By lemma we have `0 + m = m`.
            - ✅ In particular `0 + m = m -> Morphisms.respectful eq eq (Init.Nat.add (0 + m)) (Init.Nat.add m)`.
              - ❌ Using add_wd we get `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Init.Nat.add` .*by exact @add_wd*

                <details><summary>not proved</summary>

                ```
                1 goal
                  
                  n, m, p : nat
                  H :
                    forall x y : nat,
                    x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p
                  H0 : 0 + (m + p) = m + p
                  H1 : 0 + m = m
                  H2 : m + p = m + p
                  H3 : 0 + m = m
                  H4 : Morphisms.ProperProxy eq p
                  H5 : 0 + m = m
                  ============================
                  Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq))
                    Init.Nat.add
                
                File "./cyp_ko_103.v", line 4, characters 0-90:
                Error: No applicable tactic.
                ```

                </details>
            - ✅ We deduce `Morphisms.respectful eq eq (Init.Nat.add (0 + m)) (Init.Nat.add m)`.
        - ❌ In particular `0 + m + p = m + p -> Basics.flip Basics.impl (m + p = 0 + m + p) (m + p = m + p)`.

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
              CYP-OK 30
              CYP-KO 31
              CYP-OK 32
              CYP-OK 33
              CYP-OK 34
              CYP-OK 35
              CYP-KO 36
              CYP-OK 37
              CYP-OK 38
              CYP-OK 39
              CYP-OK 40
              CYP-OK 52
              CYP-KO 53
              CYP-OK 54
              CYP-OK 55
              CYP-OK 56
              CYP-OK 57
              CYP-OK 66
              CYP-OK 67
              CYP-OK 68
              CYP-KO 69
              CYP-KO 70
              CYP-OK 71
              CYP-OK 72
              CYP-OK 73
              CYP-OK 74
              CYP-OK 75
              CYP-OK 76
              CYP-OK 77
              CYP-OK 78
              CYP-KO 79
              CYP-OK 80
              CYP-KO 81
              CYP-OK 82
              CYP-OK 102
              CYP-KO 103
              CYP-OK 104
              CYP-OK 105
              CYP-OK 106
              CYP-OK 107
              File "./cyp_check.v", line 190, characters 220-247:
              Error: Cannot infer the implicit parameter A of RelationClasses.Equivalence
              whose type is "Type" in environment:
              n, m, p : nat
              
              
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
              CYP-OK 30
              CYP-KO 31
              CYP-OK 32
              CYP-OK 33
              CYP-OK 34
              CYP-OK 35
              CYP-KO 36
              CYP-OK 37
              CYP-OK 38
              CYP-OK 39
              CYP-OK 40
              CYP-OK 52
              CYP-KO 53
              CYP-OK 54
              CYP-OK 55
              CYP-OK 56
              CYP-OK 57
              CYP-OK 66
              CYP-OK 67
              CYP-OK 68
              CYP-KO 69
              CYP-KO 70
              CYP-OK 71
              CYP-OK 72
              CYP-OK 73
              CYP-OK 74
              CYP-OK 75
              CYP-OK 76
              CYP-OK 77
              CYP-OK 78
              CYP-KO 79
              CYP-OK 80
              CYP-KO 81
              CYP-OK 82
              CYP-OK 102
              CYP-KO 103
              CYP-OK 104
              CYP-OK 105
              CYP-OK 106
              CYP-OK 107
              File "./cyp_check.v", line 190, characters 220-239:
              Error: Cannot infer the implicit parameter A of RelationClasses.PER whose
              type is "Type" in environment:
              n, m, p : nat
              
              
              ```

              </details>
          - ❌ We deduce `forall x : nat, Morphisms.Proper (Morphisms.respectful eq (Basics.flip Basics.impl)) (eq x)`.

            <details><summary>Rocq error</summary>

            ```
            This step does not type-check because an earlier step does not: see the first Rocq error above.
            ```

            </details>
        - ✅ We deduce `Basics.flip Basics.impl (m + p = 0 + m + p) (m + p = m + p)`.
  - ✅ We have proved `0 + (m + p) = m + p -> Basics.flip Basics.impl (0 + (m + p) = 0 + m + p) (m + p = 0 + m + p)`.
    - ▫️ Assume `0 + (m + p) = m + p` (lemma).
      - ✅ In particular `Morphisms.ProperProxy eq (0 + m + p)`.
        - ❌ Using eq_proper_proxy we get `forall (A : Type) (x : A), Morphisms.ProperProxy eq x` .*by exact @eq_proper_proxy*

          <details><summary>not proved</summary>

          ```
          1 goal
            
            n, m, p : nat
            H :
              forall x y : nat,
              x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p
            H0 : 0 + (m + p) = m + p
            H1 : m + p = 0 + m + p
            H2 : 0 + (m + p) = m + p
            A : Type
            x : A
            ============================
            Morphisms.ProperProxy eq x
          
          File "./cyp_ko_119.v", line 4, characters 0-108:
          Error: No applicable tactic.
          ```

          </details>
      - ✅ In particular `0 + m + p = 0 + m + p -> Basics.flip Basics.impl (0 + (m + p) = 0 + m + p) (m + p = 0 + m + p)`.
        - ✅ By lemma we have `0 + (m + p) = m + p`.
        - ❌ In particular `0 + (m + p) = m + p -> Morphisms.respectful eq (Basics.flip Basics.impl) (eq (0 + (m + p))) (eq (m + p))`.

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
              CYP-OK 30
              CYP-KO 31
              CYP-OK 32
              CYP-OK 33
              CYP-OK 34
              CYP-OK 35
              CYP-KO 36
              CYP-OK 37
              CYP-OK 38
              CYP-OK 39
              CYP-OK 40
              CYP-OK 52
              CYP-KO 53
              CYP-OK 54
              CYP-OK 55
              CYP-OK 56
              CYP-OK 57
              CYP-OK 66
              CYP-OK 67
              CYP-OK 68
              CYP-KO 69
              CYP-KO 70
              CYP-OK 71
              CYP-OK 72
              CYP-OK 73
              CYP-OK 74
              CYP-OK 75
              CYP-OK 76
              CYP-OK 77
              CYP-OK 78
              CYP-KO 79
              CYP-OK 80
              CYP-KO 81
              CYP-OK 82
              CYP-OK 102
              CYP-KO 103
              CYP-OK 104
              CYP-OK 105
              CYP-OK 106
              CYP-OK 107
              CYP-OK 116
              CYP-OK 117
              CYP-OK 118
              CYP-KO 119
              CYP-OK 120
              CYP-OK 121
              File "./cyp_check.v", line 214, characters 263-290:
              Error: Cannot infer the implicit parameter A of RelationClasses.Equivalence
              whose type is "Type" in environment:
              n, m, p : nat
              
              
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
              CYP-OK 30
              CYP-KO 31
              CYP-OK 32
              CYP-OK 33
              CYP-OK 34
              CYP-OK 35
              CYP-KO 36
              CYP-OK 37
              CYP-OK 38
              CYP-OK 39
              CYP-OK 40
              CYP-OK 52
              CYP-KO 53
              CYP-OK 54
              CYP-OK 55
              CYP-OK 56
              CYP-OK 57
              CYP-OK 66
              CYP-OK 67
              CYP-OK 68
              CYP-KO 69
              CYP-KO 70
              CYP-OK 71
              CYP-OK 72
              CYP-OK 73
              CYP-OK 74
              CYP-OK 75
              CYP-OK 76
              CYP-OK 77
              CYP-OK 78
              CYP-KO 79
              CYP-OK 80
              CYP-KO 81
              CYP-OK 82
              CYP-OK 102
              CYP-KO 103
              CYP-OK 104
              CYP-OK 105
              CYP-OK 106
              CYP-OK 107
              CYP-OK 116
              CYP-OK 117
              CYP-OK 118
              CYP-KO 119
              CYP-OK 120
              CYP-OK 121
              File "./cyp_check.v", line 214, characters 263-289:
              Error: Cannot infer the implicit parameter A of RelationClasses.Transitive
              whose type is "Type" in environment:
              n, m, p : nat
              
              
              ```

              </details>
          - ❌ We deduce `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq (Basics.flip Basics.impl))) eq`.

            <details><summary>Rocq error</summary>

            ```
            This step does not type-check because an earlier step does not: see the first Rocq error above.
            ```

            </details>
        - ✅ We deduce `Morphisms.respectful eq (Basics.flip Basics.impl) (eq (0 + (m + p))) (eq (m + p))`.
      - ✅ We deduce `Basics.flip Basics.impl (0 + (m + p) = 0 + m + p) (m + p = 0 + m + p)`.
- ✅ We have `forall n0 : nat, n0 + (m + p) = n0 + m + p <-> S n0 + (m + p) = S n0 + m + p`, since `n0` is arbitrary.
  - ▫️ Let us consider an arbitrary `n0 : nat`.
    - ✅ In particular `S n0 + (m + p) = S (n0 + (m + p))`.
      - ❌ Using add_succ_l we get `forall n1 m0 : nat, S n1 + m0 = S (n1 + m0)` .*by exact @add_succ_l*

        <details><summary>not proved</summary>

        ```
        1 goal
          
          n, m, p, n0 : nat
          H :
            forall x y : nat,
            x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p
          H0 : 0 + (m + p) = 0 + m + p
          n1, m0 : nat
          ============================
          S n1 + m0 = S (n1 + m0)
        
        File "./cyp_ko_135.v", line 4, characters 0-98:
        Error: No applicable tactic.
        ```

        </details>
    - ✅ We deduce `n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S n0 + m + p`.
      - ✅ In particular `S n0 + m = S (n0 + m)`.
        - ❌ Using add_succ_l we get `forall n1 m0 : nat, S n1 + m0 = S (n1 + m0)` .*by exact @add_succ_l*

          <details><summary>not proved</summary>

          ```
          1 goal
            
            n, m, p, n0 : nat
            H :
              forall x y : nat,
              x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p
            H0 : 0 + (m + p) = 0 + m + p
            H1 : S n0 + (m + p) = S (n0 + (m + p))
            n1, m0 : nat
            ============================
            S n1 + m0 = S (n1 + m0)
          
          File "./cyp_ko_137.v", line 4, characters 0-98:
          Error: No applicable tactic.
          ```

          </details>
      - ✅ We deduce `n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S (n0 + m) + p`.
        - ✅ In particular `S (n0 + m) + p = S (n0 + m + p)`.
          - ❌ Using add_succ_l we get `forall n1 m0 : nat, S n1 + m0 = S (n1 + m0)` .*by exact @add_succ_l*

            <details><summary>not proved</summary>

            ```
            1 goal
              
              n, m, p, n0 : nat
              H :
                forall x y : nat,
                x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p
              H0 : 0 + (m + p) = 0 + m + p
              H1 : S n0 + (m + p) = S (n0 + (m + p))
              H2 : S n0 + m = S (n0 + m)
              n1, m0 : nat
              ============================
              S n1 + m0 = S (n1 + m0)
            
            File "./cyp_ko_139.v", line 4, characters 0-98:
            Error: No applicable tactic.
            ```

            </details>
        - ✅ We deduce `n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S (n0 + m + p)`.
          - ✅ In particular `S (n0 + (m + p)) = S (n0 + m + p) <-> n0 + (m + p) = n0 + m + p`.
            - ❌ Using succ_inj_wd we get `forall n1 n2 : nat, S n1 = S n2 <-> n1 = n2` .*by exact @succ_inj_wd*

              <details><summary>not proved</summary>

              ```
              1 goal
                
                n, m, p, n0 : nat
                H :
                  forall x y : nat,
                  x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p
                H0 : 0 + (m + p) = 0 + m + p
                H1 : S n0 + (m + p) = S (n0 + (m + p))
                H2 : S n0 + m = S (n0 + m)
                H3 : S (n0 + m) + p = S (n0 + m + p)
                n1, n2 : nat
                ============================
                S n1 = S n2 <-> n1 = n2
              
              File "./cyp_ko_141.v", line 4, characters 0-100:
              Error: No applicable tactic.
              ```

              </details>
          - ✅ In particular `n0 + (m + p) = n0 + m + p <-> n0 + (m + p) = n0 + m + p`.
            - ❌ Using iff_Reflexive we get `RelationClasses.Reflexive iff` .*by exact @iff_Reflexive*

              <details><summary>not proved</summary>

              ```
              1 goal
                
                n, m, p, n0 : nat
                H :
                  forall x y : nat,
                  x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p
                H0 : 0 + (m + p) = 0 + m + p
                H1 : S n0 + (m + p) = S (n0 + (m + p))
                H2 : S n0 + m = S (n0 + m)
                H3 : S (n0 + m) + p = S (n0 + m + p)
                H4 : S (n0 + (m + p)) = S (n0 + m + p) <-> n0 + (m + p) = n0 + m + p
                ============================
                RelationClasses.Reflexive iff
              
              File "./cyp_ko_143.v", line 4, characters 0-104:
              Error: No applicable tactic.
              ```

              </details>
            - ✅ In particular `RelationClasses.Reflexive iff -> forall x : Prop, x <-> x`.
              - ❌ Using reflexivity we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x : A, R x x` .*by exact @reflexivity*

                <details><summary>not proved</summary>

                ```
                1 goal
                  
                  n, m, p, n0 : nat
                  H :
                    forall x y : nat,
                    x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p
                  H0 : 0 + (m + p) = 0 + m + p
                  H1 : S n0 + (m + p) = S (n0 + (m + p))
                  H2 : S n0 + m = S (n0 + m)
                  H3 : S (n0 + m) + p = S (n0 + m + p)
                  H4 : S (n0 + (m + p)) = S (n0 + m + p) <-> n0 + (m + p) = n0 + m + p
                  H5 : RelationClasses.Reflexive iff
                  A : Type
                  R : Relation_Definitions.relation A
                  H6 : RelationClasses.Reflexive R
                  x : A
                  ============================
                  R x x
                
                File "./cyp_ko_144.v", line 4, characters 0-100:
                Error: No applicable tactic.
                ```

                </details>
            - ✅ We deduce `forall x : Prop, x <-> x`.
          - ✅ We have proved `S (n0 + (m + p)) = S (n0 + m + p) <-> n0 + (m + p) = n0 + m + p -> Basics.flip Basics.impl (n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S (n0 + m + p)) (n0 + (m + p) = n0 + m + p <-> n0 + (m + p) = n0 + m + p)`.
            - ▫️ Assume `S (n0 + (m + p)) = S (n0 + m + p) <-> n0 + (m + p) = n0 + m + p` (lemma).
              - ✅ By lemma we have `S (n0 + (m + p)) = S (n0 + m + p) <-> n0 + (m + p) = n0 + m + p`.
              - ✅ In particular `S (n0 + (m + p)) = S (n0 + m + p) <-> n0 + (m + p) = n0 + m + p -> Basics.flip Basics.impl (n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S (n0 + m + p)) (n0 + (m + p) = n0 + m + p <-> n0 + (m + p) = n0 + m + p)`.
                - ✅ We deduce `RelationClasses.PER iff`.
                  - ❌ Using iff_equivalence we get `RelationClasses.Equivalence iff` .*by exact @iff_equivalence*

                    <details><summary>not proved</summary>

                    ```
                    1 goal
                      
                      n, m, p, n0 : nat
                      H :
                        forall x y : nat,
                        x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p
                      H0 : 0 + (m + p) = 0 + m + p
                      H1 : S n0 + (m + p) = S (n0 + (m + p))
                      H2 : S n0 + m = S (n0 + m)
                      H3 : S (n0 + m) + p = S (n0 + m + p)
                      H4 : S (n0 + (m + p)) = S (n0 + m + p) <-> n0 + (m + p) = n0 + m + p
                      H5 : n0 + (m + p) = n0 + m + p <-> n0 + (m + p) = n0 + m + p
                      H6, H7 : S (n0 + (m + p)) = S (n0 + m + p) <-> n0 + (m + p) = n0 + m + p
                      ============================
                      RelationClasses.Equivalence iff
                    
                    File "./cyp_ko_149.v", line 4, characters 0-108:
                    Error: No applicable tactic.
                    ```

                    </details>
                  - ✅ In particular `RelationClasses.Equivalence iff -> RelationClasses.PER iff`.
                    - ❌ Using Equivalence_PER we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R` .*by exact @Equivalence_PER*

                      <details><summary>not proved</summary>

                      ```
                      1 goal
                        
                        n, m, p, n0 : nat
                        H :
                          forall x y : nat,
                          x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p
                        H0 : 0 + (m + p) = 0 + m + p
                        H1 : S n0 + (m + p) = S (n0 + (m + p))
                        H2 : S n0 + m = S (n0 + m)
                        H3 : S (n0 + m) + p = S (n0 + m + p)
                        H4 : S (n0 + (m + p)) = S (n0 + m + p) <-> n0 + (m + p) = n0 + m + p
                        H5 : n0 + (m + p) = n0 + m + p <-> n0 + (m + p) = n0 + m + p
                        H6, H7 : S (n0 + (m + p)) = S (n0 + m + p) <-> n0 + (m + p) = n0 + m + p
                        H8 : RelationClasses.Equivalence iff
                        A : Type
                        R : Relation_Definitions.relation A
                        H9 : RelationClasses.Equivalence R
                        ============================
                        RelationClasses.PER R
                      
                      File "./cyp_ko_150.v", line 4, characters 0-108:
                      Error: No applicable tactic.
                      ```

                      </details>
                - ✅ In particular `RelationClasses.PER iff -> forall x : Prop, Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (iff x)`.
                  - ❌ Using trans_sym_co_inv_impl_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> forall x : A, Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)` .*by exact @trans_sym_co_inv_impl_morphism*

                    <details><summary>not proved</summary>

                    ```
                    1 goal
                      
                      n, m, p, n0 : nat
                      H :
                        forall x y : nat,
                        x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p
                      H0 : 0 + (m + p) = 0 + m + p
                      H1 : S n0 + (m + p) = S (n0 + (m + p))
                      H2 : S n0 + m = S (n0 + m)
                      H3 : S (n0 + m) + p = S (n0 + m + p)
                      H4 : S (n0 + (m + p)) = S (n0 + m + p) <-> n0 + (m + p) = n0 + m + p
                      H5 : n0 + (m + p) = n0 + m + p <-> n0 + (m + p) = n0 + m + p
                      H6, H7 : S (n0 + (m + p)) = S (n0 + m + p) <-> n0 + (m + p) = n0 + m + p
                      H8 : RelationClasses.PER iff
                      A : Type
                      R : Relation_Definitions.relation A
                      H9 : RelationClasses.PER R
                      x : A
                      ============================
                      Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)
                    
                    File "./cyp_ko_153.v", line 4, characters 0-138:
                    Error: No applicable tactic.
                    ```

                    </details>
                - ✅ We deduce `forall x : Prop, Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (iff x)`.
              - ✅ We deduce `Basics.flip Basics.impl (n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S (n0 + m + p)) (n0 + (m + p) = n0 + m + p <-> n0 + (m + p) = n0 + m + p)`.
        - ✅ We have proved `S (n0 + m) + p = S (n0 + m + p) -> Basics.flip Basics.impl (n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S (n0 + m) + p) (n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S (n0 + m + p))`.
          - ▫️ Assume `S (n0 + m) + p = S (n0 + m + p)` (lemma).
            - ✅ We deduce `S (n0 + (m + p)) = S (n0 + m) + p <-> S (n0 + (m + p)) = S (n0 + m + p)`.
              - ✅ By lemma we have `S (n0 + m) + p = S (n0 + m + p)`.
              - ❌ In particular `S (n0 + m) + p = S (n0 + m + p) -> S (n0 + (m + p)) = S (n0 + m) + p <-> S (n0 + (m + p)) = S (n0 + m + p)`.

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
                    CYP-OK 30
                    CYP-KO 31
                    CYP-OK 32
                    CYP-OK 33
                    CYP-OK 34
                    CYP-OK 35
                    CYP-KO 36
                    CYP-OK 37
                    CYP-OK 38
                    CYP-OK 39
                    CYP-OK 40
                    CYP-OK 52
                    CYP-KO 53
                    CYP-OK 54
                    CYP-OK 55
                    CYP-OK 56
                    CYP-OK 57
                    CYP-OK 66
                    CYP-OK 67
                    CYP-OK 68
                    CYP-KO 69
                    CYP-KO 70
                    CYP-OK 71
                    CYP-OK 72
                    CYP-OK 73
                    CYP-OK 74
                    CYP-OK 75
                    CYP-OK 76
                    CYP-OK 77
                    CYP-OK 78
                    CYP-KO 79
                    CYP-OK 80
                    CYP-KO 81
                    CYP-OK 82
                    CYP-OK 102
                    CYP-KO 103
                    CYP-OK 104
                    CYP-OK 105
                    CYP-OK 106
                    CYP-OK 107
                    CYP-OK 116
                    CYP-OK 117
                    CYP-OK 118
                    CYP-KO 119
                    CYP-OK 120
                    CYP-OK 121
                    CYP-OK 130
                    CYP-OK 131
                    CYP-OK 132
                    CYP-OK 133
                    CYP-OK 134
                    CYP-KO 135
                    CYP-OK 136
                    CYP-KO 137
                    CYP-OK 138
                    CYP-KO 139
                    CYP-OK 140
                    CYP-KO 141
                    CYP-OK 142
                    CYP-KO 143
                    CYP-KO 144
                    CYP-OK 145
                    CYP-OK 146
                    CYP-OK 147
                    CYP-OK 148
                    CYP-KO 149
                    CYP-KO 150
                    CYP-OK 151
                    CYP-OK 152
                    CYP-KO 153
                    CYP-OK 154
                    CYP-OK 155
                    CYP-OK 156
                    CYP-OK 157
                    CYP-OK 158
                    CYP-OK 159
                    CYP-OK 160
                    File "./cyp_check.v", line 338, characters 413-440:
                    Error: Cannot infer the implicit parameter A of RelationClasses.Equivalence
                    whose type is "Type" in environment:
                    n, m, p, n0 : nat
                    
                    
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
                    CYP-OK 30
                    CYP-KO 31
                    CYP-OK 32
                    CYP-OK 33
                    CYP-OK 34
                    CYP-OK 35
                    CYP-KO 36
                    CYP-OK 37
                    CYP-OK 38
                    CYP-OK 39
                    CYP-OK 40
                    CYP-OK 52
                    CYP-KO 53
                    CYP-OK 54
                    CYP-OK 55
                    CYP-OK 56
                    CYP-OK 57
                    CYP-OK 66
                    CYP-OK 67
                    CYP-OK 68
                    CYP-KO 69
                    CYP-KO 70
                    CYP-OK 71
                    CYP-OK 72
                    CYP-OK 73
                    CYP-OK 74
                    CYP-OK 75
                    CYP-OK 76
                    CYP-OK 77
                    CYP-OK 78
                    CYP-KO 79
                    CYP-OK 80
                    CYP-KO 81
                    CYP-OK 82
                    CYP-OK 102
                    CYP-KO 103
                    CYP-OK 104
                    CYP-OK 105
                    CYP-OK 106
                    CYP-OK 107
                    CYP-OK 116
                    CYP-OK 117
                    CYP-OK 118
                    CYP-KO 119
                    CYP-OK 120
                    CYP-OK 121
                    CYP-OK 130
                    CYP-OK 131
                    CYP-OK 132
                    CYP-OK 133
                    CYP-OK 134
                    CYP-KO 135
                    CYP-OK 136
                    CYP-KO 137
                    CYP-OK 138
                    CYP-KO 139
                    CYP-OK 140
                    CYP-KO 141
                    CYP-OK 142
                    CYP-KO 143
                    CYP-KO 144
                    CYP-OK 145
                    CYP-OK 146
                    CYP-OK 147
                    CYP-OK 148
                    CYP-KO 149
                    CYP-KO 150
                    CYP-OK 151
                    CYP-OK 152
                    CYP-KO 153
                    CYP-OK 154
                    CYP-OK 155
                    CYP-OK 156
                    CYP-OK 157
                    CYP-OK 158
                    CYP-OK 159
                    CYP-OK 160
                    File "./cyp_check.v", line 338, characters 413-432:
                    Error: Cannot infer the implicit parameter A of RelationClasses.PER whose
                    type is "Type" in environment:
                    n, m, p, n0 : nat
                    
                    
                    ```

                    </details>
                - ❌ We deduce `forall x : nat, Morphisms.Proper (Morphisms.respectful eq iff) (eq x)`.

                  <details><summary>Rocq error</summary>

                  ```
                  This step does not type-check because an earlier step does not: see the first Rocq error above.
                  ```

                  </details>
            - ✅ In particular `S (n0 + (m + p)) = S (n0 + m) + p <-> S (n0 + (m + p)) = S (n0 + m + p) -> Basics.flip Basics.impl (n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S (n0 + m) + p) (n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S (n0 + m + p))`.
              - ✅ We deduce `RelationClasses.PER iff`.
                - ❌ Using iff_equivalence we get `RelationClasses.Equivalence iff` .*by exact @iff_equivalence*

                  <details><summary>not proved</summary>

                  ```
                  1 goal
                    
                    n, m, p, n0 : nat
                    H :
                      forall x y : nat,
                      x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p
                    H0 : 0 + (m + p) = 0 + m + p
                    H1 : S n0 + (m + p) = S (n0 + (m + p))
                    H2 : S n0 + m = S (n0 + m)
                    H3 : S (n0 + m) + p = S (n0 + m + p)
                    H4 : n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S (n0 + m + p)
                    H5 : S (n0 + m) + p = S (n0 + m + p)
                    H6 :
                      S (n0 + (m + p)) = S (n0 + m) + p <-> S (n0 + (m + p)) = S (n0 + m + p)
                    ============================
                    RelationClasses.Equivalence iff
                  
                  File "./cyp_ko_170.v", line 4, characters 0-108:
                  Error: No applicable tactic.
                  ```

                  </details>
                - ✅ In particular `RelationClasses.Equivalence iff -> RelationClasses.PER iff`.
                  - ❌ Using Equivalence_PER we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R` .*by exact @Equivalence_PER*

                    <details><summary>not proved</summary>

                    ```
                    1 goal
                      
                      n, m, p, n0 : nat
                      H :
                        forall x y : nat,
                        x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p
                      H0 : 0 + (m + p) = 0 + m + p
                      H1 : S n0 + (m + p) = S (n0 + (m + p))
                      H2 : S n0 + m = S (n0 + m)
                      H3 : S (n0 + m) + p = S (n0 + m + p)
                      H4 : n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S (n0 + m + p)
                      H5 : S (n0 + m) + p = S (n0 + m + p)
                      H6 :
                        S (n0 + (m + p)) = S (n0 + m) + p <-> S (n0 + (m + p)) = S (n0 + m + p)
                      H7 : RelationClasses.Equivalence iff
                      A : Type
                      R : Relation_Definitions.relation A
                      H8 : RelationClasses.Equivalence R
                      ============================
                      RelationClasses.PER R
                    
                    File "./cyp_ko_171.v", line 4, characters 0-108:
                    Error: No applicable tactic.
                    ```

                    </details>
              - ✅ In particular `RelationClasses.PER iff -> forall x : Prop, Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (iff x)`.
                - ❌ Using trans_sym_co_inv_impl_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> forall x : A, Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)` .*by exact @trans_sym_co_inv_impl_morphism*

                  <details><summary>not proved</summary>

                  ```
                  1 goal
                    
                    n, m, p, n0 : nat
                    H :
                      forall x y : nat,
                      x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p
                    H0 : 0 + (m + p) = 0 + m + p
                    H1 : S n0 + (m + p) = S (n0 + (m + p))
                    H2 : S n0 + m = S (n0 + m)
                    H3 : S (n0 + m) + p = S (n0 + m + p)
                    H4 : n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S (n0 + m + p)
                    H5 : S (n0 + m) + p = S (n0 + m + p)
                    H6 :
                      S (n0 + (m + p)) = S (n0 + m) + p <-> S (n0 + (m + p)) = S (n0 + m + p)
                    H7 : RelationClasses.PER iff
                    A : Type
                    R : Relation_Definitions.relation A
                    H8 : RelationClasses.PER R
                    x : A
                    ============================
                    Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)
                  
                  File "./cyp_ko_174.v", line 4, characters 0-138:
                  Error: No applicable tactic.
                  ```

                  </details>
              - ✅ We deduce `forall x : Prop, Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (iff x)`.
            - ✅ We deduce `Basics.flip Basics.impl (n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S (n0 + m) + p) (n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S (n0 + m + p))`.
      - ✅ We have proved `S n0 + m = S (n0 + m) -> Basics.flip Basics.impl (n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S n0 + m + p) (n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S (n0 + m) + p)`.
        - ▫️ Assume `S n0 + m = S (n0 + m)` (lemma).
          - ✅ We deduce `S (n0 + (m + p)) = S n0 + m + p <-> S (n0 + (m + p)) = S (n0 + m) + p`.
            - ✅ We deduce `S n0 + m + p = S (n0 + m) + p`.
              - ❌ In particular `Morphisms.ProperProxy eq p`.

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
                      CYP-OK 30
                      CYP-KO 31
                      CYP-OK 32
                      CYP-OK 33
                      CYP-OK 34
                      CYP-OK 35
                      CYP-KO 36
                      CYP-OK 37
                      CYP-OK 38
                      CYP-OK 39
                      CYP-OK 40
                      CYP-OK 52
                      CYP-KO 53
                      CYP-OK 54
                      CYP-OK 55
                      CYP-OK 56
                      CYP-OK 57
                      CYP-OK 66
                      CYP-OK 67
                      CYP-OK 68
                      CYP-KO 69
                      CYP-KO 70
                      CYP-OK 71
                      CYP-OK 72
                      CYP-OK 73
                      CYP-OK 74
                      CYP-OK 75
                      CYP-OK 76
                      CYP-OK 77
                      CYP-OK 78
                      CYP-KO 79
                      CYP-OK 80
                      CYP-KO 81
                      CYP-OK 82
                      CYP-OK 102
                      CYP-KO 103
                      CYP-OK 104
                      CYP-OK 105
                      CYP-OK 106
                      CYP-OK 107
                      CYP-OK 116
                      CYP-OK 117
                      CYP-OK 118
                      CYP-KO 119
                      CYP-OK 120
                      CYP-OK 121
                      CYP-OK 130
                      CYP-OK 131
                      CYP-OK 132
                      CYP-OK 133
                      CYP-OK 134
                      CYP-KO 135
                      CYP-OK 136
                      CYP-KO 137
                      CYP-OK 138
                      CYP-KO 139
                      CYP-OK 140
                      CYP-KO 141
                      CYP-OK 142
                      CYP-KO 143
                      CYP-KO 144
                      CYP-OK 145
                      CYP-OK 146
                      CYP-OK 147
                      CYP-OK 148
                      CYP-KO 149
                      CYP-KO 150
                      CYP-OK 151
                      CYP-OK 152
                      CYP-KO 153
                      CYP-OK 154
                      CYP-OK 155
                      CYP-OK 156
                      CYP-OK 157
                      CYP-OK 158
                      CYP-OK 159
                      CYP-OK 160
                      CYP-OK 169
                      CYP-KO 170
                      CYP-KO 171
                      CYP-OK 172
                      CYP-OK 173
                      CYP-KO 174
                      CYP-OK 175
                      CYP-OK 176
                      CYP-OK 177
                      CYP-OK 178
                      CYP-OK 179
                      CYP-OK 180
                      File "./cyp_check.v", line 386, characters 325-352:
                      Error: Cannot infer the implicit parameter A of RelationClasses.Equivalence
                      whose type is "Type" in environment:
                      n, m, p, n0 : nat
                      
                      
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
                      CYP-OK 30
                      CYP-KO 31
                      CYP-OK 32
                      CYP-OK 33
                      CYP-OK 34
                      CYP-OK 35
                      CYP-KO 36
                      CYP-OK 37
                      CYP-OK 38
                      CYP-OK 39
                      CYP-OK 40
                      CYP-OK 52
                      CYP-KO 53
                      CYP-OK 54
                      CYP-OK 55
                      CYP-OK 56
                      CYP-OK 57
                      CYP-OK 66
                      CYP-OK 67
                      CYP-OK 68
                      CYP-KO 69
                      CYP-KO 70
                      CYP-OK 71
                      CYP-OK 72
                      CYP-OK 73
                      CYP-OK 74
                      CYP-OK 75
                      CYP-OK 76
                      CYP-OK 77
                      CYP-OK 78
                      CYP-KO 79
                      CYP-OK 80
                      CYP-KO 81
                      CYP-OK 82
                      CYP-OK 102
                      CYP-KO 103
                      CYP-OK 104
                      CYP-OK 105
                      CYP-OK 106
                      CYP-OK 107
                      CYP-OK 116
                      CYP-OK 117
                      CYP-OK 118
                      CYP-KO 119
                      CYP-OK 120
                      CYP-OK 121
                      CYP-OK 130
                      CYP-OK 131
                      CYP-OK 132
                      CYP-OK 133
                      CYP-OK 134
                      CYP-KO 135
                      CYP-OK 136
                      CYP-KO 137
                      CYP-OK 138
                      CYP-KO 139
                      CYP-OK 140
                      CYP-KO 141
                      CYP-OK 142
                      CYP-KO 143
                      CYP-KO 144
                      CYP-OK 145
                      CYP-OK 146
                      CYP-OK 147
                      CYP-OK 148
                      CYP-KO 149
                      CYP-KO 150
                      CYP-OK 151
                      CYP-OK 152
                      CYP-KO 153
                      CYP-OK 154
                      CYP-OK 155
                      CYP-OK 156
                      CYP-OK 157
                      CYP-OK 158
                      CYP-OK 159
                      CYP-OK 160
                      CYP-OK 169
                      CYP-KO 170
                      CYP-KO 171
                      CYP-OK 172
                      CYP-OK 173
                      CYP-KO 174
                      CYP-OK 175
                      CYP-OK 176
                      CYP-OK 177
                      CYP-OK 178
                      CYP-OK 179
                      CYP-OK 180
                      File "./cyp_check.v", line 386, characters 325-350:
                      Error: Cannot infer the implicit parameter A of RelationClasses.Reflexive
                      whose type is "Type" in environment:
                      n, m, p, n0 : nat
                      
                      
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
                    CYP-OK 30
                    CYP-KO 31
                    CYP-OK 32
                    CYP-OK 33
                    CYP-OK 34
                    CYP-OK 35
                    CYP-KO 36
                    CYP-OK 37
                    CYP-OK 38
                    CYP-OK 39
                    CYP-OK 40
                    CYP-OK 52
                    CYP-KO 53
                    CYP-OK 54
                    CYP-OK 55
                    CYP-OK 56
                    CYP-OK 57
                    CYP-OK 66
                    CYP-OK 67
                    CYP-OK 68
                    CYP-KO 69
                    CYP-KO 70
                    CYP-OK 71
                    CYP-OK 72
                    CYP-OK 73
                    CYP-OK 74
                    CYP-OK 75
                    CYP-OK 76
                    CYP-OK 77
                    CYP-OK 78
                    CYP-KO 79
                    CYP-OK 80
                    CYP-KO 81
                    CYP-OK 82
                    CYP-OK 102
                    CYP-KO 103
                    CYP-OK 104
                    CYP-OK 105
                    CYP-OK 106
                    CYP-OK 107
                    CYP-OK 116
                    CYP-OK 117
                    CYP-OK 118
                    CYP-KO 119
                    CYP-OK 120
                    CYP-OK 121
                    CYP-OK 130
                    CYP-OK 131
                    CYP-OK 132
                    CYP-OK 133
                    CYP-OK 134
                    CYP-KO 135
                    CYP-OK 136
                    CYP-KO 137
                    CYP-OK 138
                    CYP-KO 139
                    CYP-OK 140
                    CYP-KO 141
                    CYP-OK 142
                    CYP-KO 143
                    CYP-KO 144
                    CYP-OK 145
                    CYP-OK 146
                    CYP-OK 147
                    CYP-OK 148
                    CYP-KO 149
                    CYP-KO 150
                    CYP-OK 151
                    CYP-OK 152
                    CYP-KO 153
                    CYP-OK 154
                    CYP-OK 155
                    CYP-OK 156
                    CYP-OK 157
                    CYP-OK 158
                    CYP-OK 159
                    CYP-OK 160
                    CYP-OK 169
                    CYP-KO 170
                    CYP-KO 171
                    CYP-OK 172
                    CYP-OK 173
                    CYP-KO 174
                    CYP-OK 175
                    CYP-OK 176
                    CYP-OK 177
                    CYP-OK 178
                    CYP-OK 179
                    CYP-OK 180
                    File "./cyp_check.v", line 386, characters 325-349:
                    Error: Cannot infer the implicit parameter A of Morphisms.ReflexiveProxy
                    whose type is "Type" in environment:
                    n, m, p, n0 : nat
                    
                    
                    ```

                    </details>
                - ❌ We deduce `forall x : nat, Morphisms.ProperProxy eq x`.

                  <details><summary>Rocq error</summary>

                  ```
                  This step does not type-check because an earlier step does not: see the first Rocq error above.
                  ```

                  </details>
              - ✅ In particular `p = p -> S n0 + m + p = S (n0 + m) + p`.
                - ✅ By lemma we have `S n0 + m = S (n0 + m)`.
                - ✅ In particular `S n0 + m = S (n0 + m) -> Morphisms.respectful eq eq (Init.Nat.add (S n0 + m)) (Init.Nat.add (S (n0 + m)))`.
                  - ❌ Using add_wd we get `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) Init.Nat.add` .*by exact @add_wd*

                    <details><summary>not proved</summary>

                    ```
                    1 goal
                      
                      n, m, p, n0 : nat
                      H :
                        forall x y : nat,
                        x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p
                      H0 : 0 + (m + p) = 0 + m + p
                      H1 : S n0 + (m + p) = S (n0 + (m + p))
                      H2 : S n0 + m = S (n0 + m)
                      H3 : n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S (n0 + m) + p
                      H4 : S n0 + m = S (n0 + m)
                      H5 : Morphisms.ProperProxy eq p
                      H6 : S n0 + m = S (n0 + m)
                      ============================
                      Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq))
                        Init.Nat.add
                    
                    File "./cyp_ko_193.v", line 4, characters 0-90:
                    Error: No applicable tactic.
                    ```

                    </details>
                - ✅ We deduce `Morphisms.respectful eq eq (Init.Nat.add (S n0 + m)) (Init.Nat.add (S (n0 + m)))`.
            - ❌ In particular `S n0 + m + p = S (n0 + m) + p -> S (n0 + (m + p)) = S n0 + m + p <-> S (n0 + (m + p)) = S (n0 + m) + p`.

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
                  CYP-OK 30
                  CYP-KO 31
                  CYP-OK 32
                  CYP-OK 33
                  CYP-OK 34
                  CYP-OK 35
                  CYP-KO 36
                  CYP-OK 37
                  CYP-OK 38
                  CYP-OK 39
                  CYP-OK 40
                  CYP-OK 52
                  CYP-KO 53
                  CYP-OK 54
                  CYP-OK 55
                  CYP-OK 56
                  CYP-OK 57
                  CYP-OK 66
                  CYP-OK 67
                  CYP-OK 68
                  CYP-KO 69
                  CYP-KO 70
                  CYP-OK 71
                  CYP-OK 72
                  CYP-OK 73
                  CYP-OK 74
                  CYP-OK 75
                  CYP-OK 76
                  CYP-OK 77
                  CYP-OK 78
                  CYP-KO 79
                  CYP-OK 80
                  CYP-KO 81
                  CYP-OK 82
                  CYP-OK 102
                  CYP-KO 103
                  CYP-OK 104
                  CYP-OK 105
                  CYP-OK 106
                  CYP-OK 107
                  CYP-OK 116
                  CYP-OK 117
                  CYP-OK 118
                  CYP-KO 119
                  CYP-OK 120
                  CYP-OK 121
                  CYP-OK 130
                  CYP-OK 131
                  CYP-OK 132
                  CYP-OK 133
                  CYP-OK 134
                  CYP-KO 135
                  CYP-OK 136
                  CYP-KO 137
                  CYP-OK 138
                  CYP-KO 139
                  CYP-OK 140
                  CYP-KO 141
                  CYP-OK 142
                  CYP-KO 143
                  CYP-KO 144
                  CYP-OK 145
                  CYP-OK 146
                  CYP-OK 147
                  CYP-OK 148
                  CYP-KO 149
                  CYP-KO 150
                  CYP-OK 151
                  CYP-OK 152
                  CYP-KO 153
                  CYP-OK 154
                  CYP-OK 155
                  CYP-OK 156
                  CYP-OK 157
                  CYP-OK 158
                  CYP-OK 159
                  CYP-OK 160
                  CYP-OK 169
                  CYP-KO 170
                  CYP-KO 171
                  CYP-OK 172
                  CYP-OK 173
                  CYP-KO 174
                  CYP-OK 175
                  CYP-OK 176
                  CYP-OK 177
                  CYP-OK 178
                  CYP-OK 179
                  CYP-OK 180
                  CYP-OK 192
                  CYP-KO 193
                  CYP-OK 194
                  CYP-OK 195
                  CYP-OK 196
                  CYP-OK 197
                  File "./cyp_check.v", line 410, characters 362-389:
                  Error: Cannot infer the implicit parameter A of RelationClasses.Equivalence
                  whose type is "Type" in environment:
                  n, m, p, n0 : nat
                  
                  
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
                  CYP-OK 30
                  CYP-KO 31
                  CYP-OK 32
                  CYP-OK 33
                  CYP-OK 34
                  CYP-OK 35
                  CYP-KO 36
                  CYP-OK 37
                  CYP-OK 38
                  CYP-OK 39
                  CYP-OK 40
                  CYP-OK 52
                  CYP-KO 53
                  CYP-OK 54
                  CYP-OK 55
                  CYP-OK 56
                  CYP-OK 57
                  CYP-OK 66
                  CYP-OK 67
                  CYP-OK 68
                  CYP-KO 69
                  CYP-KO 70
                  CYP-OK 71
                  CYP-OK 72
                  CYP-OK 73
                  CYP-OK 74
                  CYP-OK 75
                  CYP-OK 76
                  CYP-OK 77
                  CYP-OK 78
                  CYP-KO 79
                  CYP-OK 80
                  CYP-KO 81
                  CYP-OK 82
                  CYP-OK 102
                  CYP-KO 103
                  CYP-OK 104
                  CYP-OK 105
                  CYP-OK 106
                  CYP-OK 107
                  CYP-OK 116
                  CYP-OK 117
                  CYP-OK 118
                  CYP-KO 119
                  CYP-OK 120
                  CYP-OK 121
                  CYP-OK 130
                  CYP-OK 131
                  CYP-OK 132
                  CYP-OK 133
                  CYP-OK 134
                  CYP-KO 135
                  CYP-OK 136
                  CYP-KO 137
                  CYP-OK 138
                  CYP-KO 139
                  CYP-OK 140
                  CYP-KO 141
                  CYP-OK 142
                  CYP-KO 143
                  CYP-KO 144
                  CYP-OK 145
                  CYP-OK 146
                  CYP-OK 147
                  CYP-OK 148
                  CYP-KO 149
                  CYP-KO 150
                  CYP-OK 151
                  CYP-OK 152
                  CYP-KO 153
                  CYP-OK 154
                  CYP-OK 155
                  CYP-OK 156
                  CYP-OK 157
                  CYP-OK 158
                  CYP-OK 159
                  CYP-OK 160
                  CYP-OK 169
                  CYP-KO 170
                  CYP-KO 171
                  CYP-OK 172
                  CYP-OK 173
                  CYP-KO 174
                  CYP-OK 175
                  CYP-OK 176
                  CYP-OK 177
                  CYP-OK 178
                  CYP-OK 179
                  CYP-OK 180
                  CYP-OK 192
                  CYP-KO 193
                  CYP-OK 194
                  CYP-OK 195
                  CYP-OK 196
                  CYP-OK 197
                  File "./cyp_check.v", line 410, characters 362-381:
                  Error: Cannot infer the implicit parameter A of RelationClasses.PER whose
                  type is "Type" in environment:
                  n, m, p, n0 : nat
                  
                  
                  ```

                  </details>
              - ❌ We deduce `forall x : nat, Morphisms.Proper (Morphisms.respectful eq iff) (eq x)`.

                <details><summary>Rocq error</summary>

                ```
                This step does not type-check because an earlier step does not: see the first Rocq error above.
                ```

                </details>
          - ✅ In particular `S (n0 + (m + p)) = S n0 + m + p <-> S (n0 + (m + p)) = S (n0 + m) + p -> Basics.flip Basics.impl (n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S n0 + m + p) (n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S (n0 + m) + p)`.
            - ✅ We deduce `RelationClasses.PER iff`.
              - ❌ Using iff_equivalence we get `RelationClasses.Equivalence iff` .*by exact @iff_equivalence*

                <details><summary>not proved</summary>

                ```
                1 goal
                  
                  n, m, p, n0 : nat
                  H :
                    forall x y : nat,
                    x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p
                  H0 : 0 + (m + p) = 0 + m + p
                  H1 : S n0 + (m + p) = S (n0 + (m + p))
                  H2 : S n0 + m = S (n0 + m)
                  H3 : n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S (n0 + m) + p
                  H4 : S n0 + m = S (n0 + m)
                  H5 : S (n0 + (m + p)) = S n0 + m + p <-> S (n0 + (m + p)) = S (n0 + m) + p
                  ============================
                  RelationClasses.Equivalence iff
                
                File "./cyp_ko_207.v", line 4, characters 0-108:
                Error: No applicable tactic.
                ```

                </details>
              - ✅ In particular `RelationClasses.Equivalence iff -> RelationClasses.PER iff`.
                - ❌ Using Equivalence_PER we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R` .*by exact @Equivalence_PER*

                  <details><summary>not proved</summary>

                  ```
                  1 goal
                    
                    n, m, p, n0 : nat
                    H :
                      forall x y : nat,
                      x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p
                    H0 : 0 + (m + p) = 0 + m + p
                    H1 : S n0 + (m + p) = S (n0 + (m + p))
                    H2 : S n0 + m = S (n0 + m)
                    H3 : n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S (n0 + m) + p
                    H4 : S n0 + m = S (n0 + m)
                    H5 : S (n0 + (m + p)) = S n0 + m + p <-> S (n0 + (m + p)) = S (n0 + m) + p
                    H6 : RelationClasses.Equivalence iff
                    A : Type
                    R : Relation_Definitions.relation A
                    H7 : RelationClasses.Equivalence R
                    ============================
                    RelationClasses.PER R
                  
                  File "./cyp_ko_208.v", line 4, characters 0-108:
                  Error: No applicable tactic.
                  ```

                  </details>
            - ✅ In particular `RelationClasses.PER iff -> forall x : Prop, Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (iff x)`.
              - ❌ Using trans_sym_co_inv_impl_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> forall x : A, Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)` .*by exact @trans_sym_co_inv_impl_morphism*

                <details><summary>not proved</summary>

                ```
                1 goal
                  
                  n, m, p, n0 : nat
                  H :
                    forall x y : nat,
                    x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p
                  H0 : 0 + (m + p) = 0 + m + p
                  H1 : S n0 + (m + p) = S (n0 + (m + p))
                  H2 : S n0 + m = S (n0 + m)
                  H3 : n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S (n0 + m) + p
                  H4 : S n0 + m = S (n0 + m)
                  H5 : S (n0 + (m + p)) = S n0 + m + p <-> S (n0 + (m + p)) = S (n0 + m) + p
                  H6 : RelationClasses.PER iff
                  A : Type
                  R : Relation_Definitions.relation A
                  H7 : RelationClasses.PER R
                  x : A
                  ============================
                  Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)
                
                File "./cyp_ko_211.v", line 4, characters 0-138:
                Error: No applicable tactic.
                ```

                </details>
            - ✅ We deduce `forall x : Prop, Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (iff x)`.
          - ✅ We deduce `Basics.flip Basics.impl (n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S n0 + m + p) (n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S (n0 + m) + p)`.
    - ✅ We have proved `S n0 + (m + p) = S (n0 + (m + p)) -> Basics.flip Basics.impl (n0 + (m + p) = n0 + m + p <-> S n0 + (m + p) = S n0 + m + p) (n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S n0 + m + p)`.
      - ▫️ Assume `S n0 + (m + p) = S (n0 + (m + p))` (lemma).
        - ✅ We deduce `S n0 + (m + p) = S n0 + m + p <-> S (n0 + (m + p)) = S n0 + m + p`.
          - ❌ In particular `Morphisms.ProperProxy eq (S n0 + m + p)`.

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
                  CYP-OK 30
                  CYP-KO 31
                  CYP-OK 32
                  CYP-OK 33
                  CYP-OK 34
                  CYP-OK 35
                  CYP-KO 36
                  CYP-OK 37
                  CYP-OK 38
                  CYP-OK 39
                  CYP-OK 40
                  CYP-OK 52
                  CYP-KO 53
                  CYP-OK 54
                  CYP-OK 55
                  CYP-OK 56
                  CYP-OK 57
                  CYP-OK 66
                  CYP-OK 67
                  CYP-OK 68
                  CYP-KO 69
                  CYP-KO 70
                  CYP-OK 71
                  CYP-OK 72
                  CYP-OK 73
                  CYP-OK 74
                  CYP-OK 75
                  CYP-OK 76
                  CYP-OK 77
                  CYP-OK 78
                  CYP-KO 79
                  CYP-OK 80
                  CYP-KO 81
                  CYP-OK 82
                  CYP-OK 102
                  CYP-KO 103
                  CYP-OK 104
                  CYP-OK 105
                  CYP-OK 106
                  CYP-OK 107
                  CYP-OK 116
                  CYP-OK 117
                  CYP-OK 118
                  CYP-KO 119
                  CYP-OK 120
                  CYP-OK 121
                  CYP-OK 130
                  CYP-OK 131
                  CYP-OK 132
                  CYP-OK 133
                  CYP-OK 134
                  CYP-KO 135
                  CYP-OK 136
                  CYP-KO 137
                  CYP-OK 138
                  CYP-KO 139
                  CYP-OK 140
                  CYP-KO 141
                  CYP-OK 142
                  CYP-KO 143
                  CYP-KO 144
                  CYP-OK 145
                  CYP-OK 146
                  CYP-OK 147
                  CYP-OK 148
                  CYP-KO 149
                  CYP-KO 150
                  CYP-OK 151
                  CYP-OK 152
                  CYP-KO 153
                  CYP-OK 154
                  CYP-OK 155
                  CYP-OK 156
                  CYP-OK 157
                  CYP-OK 158
                  CYP-OK 159
                  CYP-OK 160
                  CYP-OK 169
                  CYP-KO 170
                  CYP-KO 171
                  CYP-OK 172
                  CYP-OK 173
                  CYP-KO 174
                  CYP-OK 175
                  CYP-OK 176
                  CYP-OK 177
                  CYP-OK 178
                  CYP-OK 179
                  CYP-OK 180
                  CYP-OK 192
                  CYP-KO 193
                  CYP-OK 194
                  CYP-OK 195
                  CYP-OK 196
                  CYP-OK 197
                  CYP-OK 206
                  CYP-KO 207
                  CYP-KO 208
                  CYP-OK 209
                  CYP-OK 210
                  CYP-KO 211
                  CYP-OK 212
                  CYP-OK 213
                  CYP-OK 214
                  CYP-OK 215
                  CYP-OK 216
                  CYP-OK 217
                  File "./cyp_check.v", line 458, characters 306-333:
                  Error: Cannot infer the implicit parameter A of RelationClasses.Equivalence
                  whose type is "Type" in environment:
                  n, m, p, n0 : nat
                  
                  
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
                  CYP-OK 30
                  CYP-KO 31
                  CYP-OK 32
                  CYP-OK 33
                  CYP-OK 34
                  CYP-OK 35
                  CYP-KO 36
                  CYP-OK 37
                  CYP-OK 38
                  CYP-OK 39
                  CYP-OK 40
                  CYP-OK 52
                  CYP-KO 53
                  CYP-OK 54
                  CYP-OK 55
                  CYP-OK 56
                  CYP-OK 57
                  CYP-OK 66
                  CYP-OK 67
                  CYP-OK 68
                  CYP-KO 69
                  CYP-KO 70
                  CYP-OK 71
                  CYP-OK 72
                  CYP-OK 73
                  CYP-OK 74
                  CYP-OK 75
                  CYP-OK 76
                  CYP-OK 77
                  CYP-OK 78
                  CYP-KO 79
                  CYP-OK 80
                  CYP-KO 81
                  CYP-OK 82
                  CYP-OK 102
                  CYP-KO 103
                  CYP-OK 104
                  CYP-OK 105
                  CYP-OK 106
                  CYP-OK 107
                  CYP-OK 116
                  CYP-OK 117
                  CYP-OK 118
                  CYP-KO 119
                  CYP-OK 120
                  CYP-OK 121
                  CYP-OK 130
                  CYP-OK 131
                  CYP-OK 132
                  CYP-OK 133
                  CYP-OK 134
                  CYP-KO 135
                  CYP-OK 136
                  CYP-KO 137
                  CYP-OK 138
                  CYP-KO 139
                  CYP-OK 140
                  CYP-KO 141
                  CYP-OK 142
                  CYP-KO 143
                  CYP-KO 144
                  CYP-OK 145
                  CYP-OK 146
                  CYP-OK 147
                  CYP-OK 148
                  CYP-KO 149
                  CYP-KO 150
                  CYP-OK 151
                  CYP-OK 152
                  CYP-KO 153
                  CYP-OK 154
                  CYP-OK 155
                  CYP-OK 156
                  CYP-OK 157
                  CYP-OK 158
                  CYP-OK 159
                  CYP-OK 160
                  CYP-OK 169
                  CYP-KO 170
                  CYP-KO 171
                  CYP-OK 172
                  CYP-OK 173
                  CYP-KO 174
                  CYP-OK 175
                  CYP-OK 176
                  CYP-OK 177
                  CYP-OK 178
                  CYP-OK 179
                  CYP-OK 180
                  CYP-OK 192
                  CYP-KO 193
                  CYP-OK 194
                  CYP-OK 195
                  CYP-OK 196
                  CYP-OK 197
                  CYP-OK 206
                  CYP-KO 207
                  CYP-KO 208
                  CYP-OK 209
                  CYP-OK 210
                  CYP-KO 211
                  CYP-OK 212
                  CYP-OK 213
                  CYP-OK 214
                  CYP-OK 215
                  CYP-OK 216
                  CYP-OK 217
                  File "./cyp_check.v", line 458, characters 306-331:
                  Error: Cannot infer the implicit parameter A of RelationClasses.Reflexive
                  whose type is "Type" in environment:
                  n, m, p, n0 : nat
                  
                  
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
                CYP-OK 30
                CYP-KO 31
                CYP-OK 32
                CYP-OK 33
                CYP-OK 34
                CYP-OK 35
                CYP-KO 36
                CYP-OK 37
                CYP-OK 38
                CYP-OK 39
                CYP-OK 40
                CYP-OK 52
                CYP-KO 53
                CYP-OK 54
                CYP-OK 55
                CYP-OK 56
                CYP-OK 57
                CYP-OK 66
                CYP-OK 67
                CYP-OK 68
                CYP-KO 69
                CYP-KO 70
                CYP-OK 71
                CYP-OK 72
                CYP-OK 73
                CYP-OK 74
                CYP-OK 75
                CYP-OK 76
                CYP-OK 77
                CYP-OK 78
                CYP-KO 79
                CYP-OK 80
                CYP-KO 81
                CYP-OK 82
                CYP-OK 102
                CYP-KO 103
                CYP-OK 104
                CYP-OK 105
                CYP-OK 106
                CYP-OK 107
                CYP-OK 116
                CYP-OK 117
                CYP-OK 118
                CYP-KO 119
                CYP-OK 120
                CYP-OK 121
                CYP-OK 130
                CYP-OK 131
                CYP-OK 132
                CYP-OK 133
                CYP-OK 134
                CYP-KO 135
                CYP-OK 136
                CYP-KO 137
                CYP-OK 138
                CYP-KO 139
                CYP-OK 140
                CYP-KO 141
                CYP-OK 142
                CYP-KO 143
                CYP-KO 144
                CYP-OK 145
                CYP-OK 146
                CYP-OK 147
                CYP-OK 148
                CYP-KO 149
                CYP-KO 150
                CYP-OK 151
                CYP-OK 152
                CYP-KO 153
                CYP-OK 154
                CYP-OK 155
                CYP-OK 156
                CYP-OK 157
                CYP-OK 158
                CYP-OK 159
                CYP-OK 160
                CYP-OK 169
                CYP-KO 170
                CYP-KO 171
                CYP-OK 172
                CYP-OK 173
                CYP-KO 174
                CYP-OK 175
                CYP-OK 176
                CYP-OK 177
                CYP-OK 178
                CYP-OK 179
                CYP-OK 180
                CYP-OK 192
                CYP-KO 193
                CYP-OK 194
                CYP-OK 195
                CYP-OK 196
                CYP-OK 197
                CYP-OK 206
                CYP-KO 207
                CYP-KO 208
                CYP-OK 209
                CYP-OK 210
                CYP-KO 211
                CYP-OK 212
                CYP-OK 213
                CYP-OK 214
                CYP-OK 215
                CYP-OK 216
                CYP-OK 217
                File "./cyp_check.v", line 458, characters 306-330:
                Error: Cannot infer the implicit parameter A of Morphisms.ReflexiveProxy
                whose type is "Type" in environment:
                n, m, p, n0 : nat
                
                
                ```

                </details>
            - ❌ We deduce `forall x : nat, Morphisms.ProperProxy eq x`.

              <details><summary>Rocq error</summary>

              ```
              This step does not type-check because an earlier step does not: see the first Rocq error above.
              ```

              </details>
          - ✅ In particular `S n0 + m + p = S n0 + m + p -> S n0 + (m + p) = S n0 + m + p <-> S (n0 + (m + p)) = S n0 + m + p`.
            - ✅ By lemma we have `S n0 + (m + p) = S (n0 + (m + p))`.
            - ❌ In particular `S n0 + (m + p) = S (n0 + (m + p)) -> Morphisms.respectful eq iff (eq (S n0 + (m + p))) (eq (S (n0 + (m + p))))`.

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
                  CYP-OK 30
                  CYP-KO 31
                  CYP-OK 32
                  CYP-OK 33
                  CYP-OK 34
                  CYP-OK 35
                  CYP-KO 36
                  CYP-OK 37
                  CYP-OK 38
                  CYP-OK 39
                  CYP-OK 40
                  CYP-OK 52
                  CYP-KO 53
                  CYP-OK 54
                  CYP-OK 55
                  CYP-OK 56
                  CYP-OK 57
                  CYP-OK 66
                  CYP-OK 67
                  CYP-OK 68
                  CYP-KO 69
                  CYP-KO 70
                  CYP-OK 71
                  CYP-OK 72
                  CYP-OK 73
                  CYP-OK 74
                  CYP-OK 75
                  CYP-OK 76
                  CYP-OK 77
                  CYP-OK 78
                  CYP-KO 79
                  CYP-OK 80
                  CYP-KO 81
                  CYP-OK 82
                  CYP-OK 102
                  CYP-KO 103
                  CYP-OK 104
                  CYP-OK 105
                  CYP-OK 106
                  CYP-OK 107
                  CYP-OK 116
                  CYP-OK 117
                  CYP-OK 118
                  CYP-KO 119
                  CYP-OK 120
                  CYP-OK 121
                  CYP-OK 130
                  CYP-OK 131
                  CYP-OK 132
                  CYP-OK 133
                  CYP-OK 134
                  CYP-KO 135
                  CYP-OK 136
                  CYP-KO 137
                  CYP-OK 138
                  CYP-KO 139
                  CYP-OK 140
                  CYP-KO 141
                  CYP-OK 142
                  CYP-KO 143
                  CYP-KO 144
                  CYP-OK 145
                  CYP-OK 146
                  CYP-OK 147
                  CYP-OK 148
                  CYP-KO 149
                  CYP-KO 150
                  CYP-OK 151
                  CYP-OK 152
                  CYP-KO 153
                  CYP-OK 154
                  CYP-OK 155
                  CYP-OK 156
                  CYP-OK 157
                  CYP-OK 158
                  CYP-OK 159
                  CYP-OK 160
                  CYP-OK 169
                  CYP-KO 170
                  CYP-KO 171
                  CYP-OK 172
                  CYP-OK 173
                  CYP-KO 174
                  CYP-OK 175
                  CYP-OK 176
                  CYP-OK 177
                  CYP-OK 178
                  CYP-OK 179
                  CYP-OK 180
                  CYP-OK 192
                  CYP-KO 193
                  CYP-OK 194
                  CYP-OK 195
                  CYP-OK 196
                  CYP-OK 197
                  CYP-OK 206
                  CYP-KO 207
                  CYP-KO 208
                  CYP-OK 209
                  CYP-OK 210
                  CYP-KO 211
                  CYP-OK 212
                  CYP-OK 213
                  CYP-OK 214
                  CYP-OK 215
                  CYP-OK 216
                  CYP-OK 217
                  CYP-OK 229
                  File "./cyp_check.v", line 462, characters 394-421:
                  Error: Cannot infer the implicit parameter A of RelationClasses.Equivalence
                  whose type is "Type" in environment:
                  n, m, p, n0 : nat
                  
                  
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
                  CYP-OK 30
                  CYP-KO 31
                  CYP-OK 32
                  CYP-OK 33
                  CYP-OK 34
                  CYP-OK 35
                  CYP-KO 36
                  CYP-OK 37
                  CYP-OK 38
                  CYP-OK 39
                  CYP-OK 40
                  CYP-OK 52
                  CYP-KO 53
                  CYP-OK 54
                  CYP-OK 55
                  CYP-OK 56
                  CYP-OK 57
                  CYP-OK 66
                  CYP-OK 67
                  CYP-OK 68
                  CYP-KO 69
                  CYP-KO 70
                  CYP-OK 71
                  CYP-OK 72
                  CYP-OK 73
                  CYP-OK 74
                  CYP-OK 75
                  CYP-OK 76
                  CYP-OK 77
                  CYP-OK 78
                  CYP-KO 79
                  CYP-OK 80
                  CYP-KO 81
                  CYP-OK 82
                  CYP-OK 102
                  CYP-KO 103
                  CYP-OK 104
                  CYP-OK 105
                  CYP-OK 106
                  CYP-OK 107
                  CYP-OK 116
                  CYP-OK 117
                  CYP-OK 118
                  CYP-KO 119
                  CYP-OK 120
                  CYP-OK 121
                  CYP-OK 130
                  CYP-OK 131
                  CYP-OK 132
                  CYP-OK 133
                  CYP-OK 134
                  CYP-KO 135
                  CYP-OK 136
                  CYP-KO 137
                  CYP-OK 138
                  CYP-KO 139
                  CYP-OK 140
                  CYP-KO 141
                  CYP-OK 142
                  CYP-KO 143
                  CYP-KO 144
                  CYP-OK 145
                  CYP-OK 146
                  CYP-OK 147
                  CYP-OK 148
                  CYP-KO 149
                  CYP-KO 150
                  CYP-OK 151
                  CYP-OK 152
                  CYP-KO 153
                  CYP-OK 154
                  CYP-OK 155
                  CYP-OK 156
                  CYP-OK 157
                  CYP-OK 158
                  CYP-OK 159
                  CYP-OK 160
                  CYP-OK 169
                  CYP-KO 170
                  CYP-KO 171
                  CYP-OK 172
                  CYP-OK 173
                  CYP-KO 174
                  CYP-OK 175
                  CYP-OK 176
                  CYP-OK 177
                  CYP-OK 178
                  CYP-OK 179
                  CYP-OK 180
                  CYP-OK 192
                  CYP-KO 193
                  CYP-OK 194
                  CYP-OK 195
                  CYP-OK 196
                  CYP-OK 197
                  CYP-OK 206
                  CYP-KO 207
                  CYP-KO 208
                  CYP-OK 209
                  CYP-OK 210
                  CYP-KO 211
                  CYP-OK 212
                  CYP-OK 213
                  CYP-OK 214
                  CYP-OK 215
                  CYP-OK 216
                  CYP-OK 217
                  CYP-OK 229
                  File "./cyp_check.v", line 462, characters 394-413:
                  Error: Cannot infer the implicit parameter A of RelationClasses.PER whose
                  type is "Type" in environment:
                  n, m, p, n0 : nat
                  
                  
                  ```

                  </details>
              - ❌ We deduce `Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq iff)) eq`.

                <details><summary>Rocq error</summary>

                ```
                This step does not type-check because an earlier step does not: see the first Rocq error above.
                ```

                </details>
            - ✅ We deduce `Morphisms.respectful eq iff (eq (S n0 + (m + p))) (eq (S (n0 + (m + p))))`.
        - ✅ In particular `S n0 + (m + p) = S n0 + m + p <-> S (n0 + (m + p)) = S n0 + m + p -> Basics.flip Basics.impl (n0 + (m + p) = n0 + m + p <-> S n0 + (m + p) = S n0 + m + p) (n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S n0 + m + p)`.
          - ✅ We deduce `RelationClasses.PER iff`.
            - ❌ Using iff_equivalence we get `RelationClasses.Equivalence iff` .*by exact @iff_equivalence*

              <details><summary>not proved</summary>

              ```
              1 goal
                
                n, m, p, n0 : nat
                H :
                  forall x y : nat,
                  x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p
                H0 : 0 + (m + p) = 0 + m + p
                H1 : S n0 + (m + p) = S (n0 + (m + p))
                H2 : n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S n0 + m + p
                H3 : S n0 + (m + p) = S (n0 + (m + p))
                H4 : S n0 + (m + p) = S n0 + m + p <-> S (n0 + (m + p)) = S n0 + m + p
                ============================
                RelationClasses.Equivalence iff
              
              File "./cyp_ko_241.v", line 4, characters 0-108:
              Error: No applicable tactic.
              ```

              </details>
            - ✅ In particular `RelationClasses.Equivalence iff -> RelationClasses.PER iff`.
              - ❌ Using Equivalence_PER we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.PER R` .*by exact @Equivalence_PER*

                <details><summary>not proved</summary>

                ```
                1 goal
                  
                  n, m, p, n0 : nat
                  H :
                    forall x y : nat,
                    x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p
                  H0 : 0 + (m + p) = 0 + m + p
                  H1 : S n0 + (m + p) = S (n0 + (m + p))
                  H2 : n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S n0 + m + p
                  H3 : S n0 + (m + p) = S (n0 + (m + p))
                  H4 : S n0 + (m + p) = S n0 + m + p <-> S (n0 + (m + p)) = S n0 + m + p
                  H5 : RelationClasses.Equivalence iff
                  A : Type
                  R : Relation_Definitions.relation A
                  H6 : RelationClasses.Equivalence R
                  ============================
                  RelationClasses.PER R
                
                File "./cyp_ko_242.v", line 4, characters 0-108:
                Error: No applicable tactic.
                ```

                </details>
          - ✅ In particular `RelationClasses.PER iff -> forall x : Prop, Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (iff x)`.
            - ❌ Using trans_sym_co_inv_impl_morphism we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.PER R -> forall x : A, Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)` .*by exact @trans_sym_co_inv_impl_morphism*

              <details><summary>not proved</summary>

              ```
              1 goal
                
                n, m, p, n0 : nat
                H :
                  forall x y : nat,
                  x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p
                H0 : 0 + (m + p) = 0 + m + p
                H1 : S n0 + (m + p) = S (n0 + (m + p))
                H2 : n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S n0 + m + p
                H3 : S n0 + (m + p) = S (n0 + (m + p))
                H4 : S n0 + (m + p) = S n0 + m + p <-> S (n0 + (m + p)) = S n0 + m + p
                H5 : RelationClasses.PER iff
                A : Type
                R : Relation_Definitions.relation A
                H6 : RelationClasses.PER R
                x : A
                ============================
                Morphisms.Proper (Morphisms.respectful R (Basics.flip Basics.impl)) (R x)
              
              File "./cyp_ko_245.v", line 4, characters 0-138:
              Error: No applicable tactic.
              ```

              </details>
          - ✅ We deduce `forall x : Prop, Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) (iff x)`.
        - ✅ We deduce `Basics.flip Basics.impl (n0 + (m + p) = n0 + m + p <-> S n0 + (m + p) = S n0 + m + p) (n0 + (m + p) = n0 + m + p <-> S (n0 + (m + p)) = S n0 + m + p)`.
    - ✅ We deduce `n0 + (m + p) = n0 + m + p <-> S n0 + (m + p) = S n0 + m + p`.
- ✅ In particular `Morphisms.Proper (Morphisms.respectful eq iff) (fun t : nat => t + (m + p) = t + m + p) -> 0 + (m + p) = 0 + m + p -> (forall n0 : nat, n0 + (m + p) = n0 + m + p <-> S n0 + (m + p) = S n0 + m + p) -> forall n0 : nat, n0 + (m + p) = n0 + m + p`.
  - ❌ Using bi_induction we get `forall A : nat -> Prop, Morphisms.Proper (Morphisms.respectful eq iff) A -> A 0 -> (forall n0 : nat, A n0 <-> A (S n0)) -> forall n0 : nat, A n0` .*by exact @bi_induction*

    <details><summary>not proved</summary>

    ```
    1 goal
      
      n, m, p : nat
      H :
        forall x y : nat,
        x = y -> x + (m + p) = x + m + p <-> y + (m + p) = y + m + p
      H0 : 0 + (m + p) = 0 + m + p
      H1 :
        forall n0 : nat,
        n0 + (m + p) = n0 + m + p <-> S n0 + (m + p) = S n0 + m + p
      A : nat -> Prop
      H2 : Morphisms.Proper (Morphisms.respectful eq iff) A
      H3 : A 0
      H4 : forall n0 : nat, A n0 <-> A (S n0)
      n0 : nat
      ============================
      A n0
    
    File "./cyp_ko_253.v", line 4, characters 0-102:
    Error: No applicable tactic.
    ```

    </details>
- ✅ We deduce `forall n0 : nat, n0 + (m + p) = n0 + m + p`.
- ✅ In particular `n + (m + p) = n + m + p`.

