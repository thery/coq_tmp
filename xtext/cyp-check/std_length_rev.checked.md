<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# length_rev

❌ Let `A : Type`. Let `l : list A`. We prove `length (rev l) = length l`.

<details><summary>Rocq error</summary>

```
This step does not type-check because an earlier step does not: see the first Rocq error above.
```

</details>

- ▫️ To prove `length (rev l) = length l` by induction (list, list_ind), we generalise it to `forall l0 : list A, length (rev l0) = length l0`:
- ❌ Case 1 (base): we prove `length (rev nil) = length nil`.

  <details><summary>Rocq error</summary>

  ```
  CYP-OK 1
  File "./cyp_check.v", line 6, characters 52-58:
  Error: Cannot infer the implicit parameter A of length whose type is 
  "Type" in environment:
  A : Type
  l : list A
  
  
  ```

  </details>
  - ✅ By definition of eq (eq_refl), we have `0 = 0` .*by eapply @eq_refl; eauto*
- ❌ Case 2 (inductive): we prove `forall (a : A) (l0 : list A), length (rev l0) = length l0 -> length (rev (a :: l0)) = length (a :: l0)`.

  <details><summary>Rocq error</summary>

  ```
  This step does not type-check because an earlier step does not: see the first Rocq error above.
  ```

  </details>
  - ▫️ Let `a : A`.
  - ▫️ Let `l0 : list A`.
  - ▫️ Assume by induction hypothesis `length (rev l0) = length l0` (IHl).
    - ❌ Rewriting with `length (rev l0) = length l0` from right to left (eq_ind_r), we get `length (rev l0) + length (a :: nil) = S (length l0)`.

      <details><summary>Rocq error</summary>

      ```
      This step does not type-check because an earlier step does not: see the first Rocq error above.
      ```

      </details>
      - ❌ Rewriting with `length l0 + length (a :: nil) = length (a :: nil) + length l0` from right to left (eq_ind_r), we get `length l0 + length (a :: nil) = S (length l0)`.

        <details><summary>Rocq error</summary>

        ```
        This step does not type-check because an earlier step does not: see the first Rocq error above.
        ```

        </details>
        - ❌ By definition of eq (eq_refl), we have `S (length l0) = S (length l0)` .*by eapply @eq_refl; eauto*

          <details><summary>Rocq error</summary>

          ```
          CYP-OK 1
          File "./cyp_check.v", line 6, characters 61-67:
          Error: Cannot infer the implicit parameter A of length whose type is 
          "Type" in environment:
          A : Type
          l : list A
          a : A
          l0 : list A
          
          
          ```

          </details>
        - ❌ In particular `length l0 + length (a :: nil) = length (a :: nil) + length l0`.

          <details><summary>Rocq error</summary>

          ```
          This step does not type-check because an earlier step does not: see the first Rocq error above.
          ```

          </details>
          - ❌ Using add_comm we get `forall n m : nat, n + m = m + n` .*by exact @add_comm*

            <details><summary>Rocq error</summary>

            ```
            This step does not type-check because an earlier step does not: see the first Rocq error above.
            ```

            </details>
      - ❌ By IHl we have `length (rev l0) = length l0`.

        <details><summary>Rocq error</summary>

        ```
        This step does not type-check because an earlier step does not: see the first Rocq error above.
        ```

        </details>
    - ❌ In particular `length (rev l0 ++ a :: nil) = length (rev l0) + length (a :: nil)`.

      <details><summary>Rocq error</summary>

      ```
      This step does not type-check because an earlier step does not: see the first Rocq error above.
      ```

      </details>
      - ❌ Using length_app we get `forall (A0 : Type) (l1 l' : list A0), length (l1 ++ l') = length l1 + length l'` .*by exact @length_app*

        <details><summary>Rocq error</summary>

        ```
        This step does not type-check because an earlier step does not: see the first Rocq error above.
        ```

        </details>
    - ❌ Rewriting with `length (rev l0 ++ a :: nil) = length (rev l0) + length (a :: nil)` from right to left (eq_ind_r), we get `length (rev l0 ++ a :: nil) = S (length l0)`.

      <details><summary>Rocq error</summary>

      ```
      This step does not type-check because an earlier step does not: see the first Rocq error above.
      ```

      </details>
- ❌ These cases being exhaustive, we deduce `forall l0 : list A, length (rev l0) = length l0` .*by eapply (@list_ind (A) (fun l0 : list A => length (rev l0) = length l0)); cbv beta; eauto*

  <details><summary>Rocq error</summary>

  ```
  This step does not type-check because an earlier step does not: see the first Rocq error above.
  ```

  </details>
- ❌ In particular `length (rev l) = length l`.

  <details><summary>Rocq error</summary>

  ```
  This step does not type-check because an earlier step does not: see the first Rocq error above.
  ```

  </details>

