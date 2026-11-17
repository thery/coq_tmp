<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# Nat.le_refl

✅ Let `n : nat`. We prove `n <= n`.

- ✅ Thus we have `forall n0 m : nat, n0 < m \/ n0 = m -> n0 <= m` (H).
  - ▫️ Let us choose arbitrarily `n0 : nat`, `m : nat`.
    - ❌ Using lt_eq_cases we get `forall n1 m0 : nat, n1 <= m0 <-> n1 < m0 \/ n1 = m0` .*by exact @lt_eq_cases*

      <details><summary>not proved</summary>

      ```
      1 goal
        
        n, n0, m, n1, m0 : nat
        ============================
        n1 <= m0 <-> n1 < m0 \/ n1 = m0
      
      File "./cyp_ko_1.v", line 4, characters 0-100:
      Error: No applicable tactic.
      ```

      </details>
    - ✅ In particular `n0 <= m <-> n0 < m \/ n0 = m`.
    - ✅ Going back to the definition of and (match) in `n0 <= m <-> n0 < m \/ n0 = m`, we prove `n0 < m \/ n0 = m -> n0 <= m`:
      - ▫️ Assume `n0 <= m -> n0 < m \/ n0 = m` (h) and `n0 < m \/ n0 = m -> n0 <= m` (h0).
        - ✅ By h0 we have `n0 < m \/ n0 = m -> n0 <= m`.
- ❌ By definition of or (or_intror), we have `n < n \/ n = n` .*by eapply @or_intror; eauto*

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
      CYP-OK 3
      CYP-OK 4
      CYP-OK 5
      File "./cyp_check.v", line 22, characters 79-106:
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
      CYP-OK 3
      CYP-OK 4
      CYP-OK 5
      File "./cyp_check.v", line 22, characters 79-104:
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
  - ❌ In particular `n = n`.

    <details><summary>Rocq error</summary>

    ```
    This step does not type-check because an earlier step does not: see the first Rocq error above.
    ```

    </details>
- ✅ In particular `n < n \/ n = n -> n <= n`.
  - ✅ By H we have `forall n0 m : nat, n0 < m \/ n0 = m -> n0 <= m`.
- ✅ We deduce `n <= n`.

