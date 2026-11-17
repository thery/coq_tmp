<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List. Import ListNotations. Require Import XText.inductive. -->

# length_app'

✅ We prove `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`.

- ❌ We prove `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2` by recursion on `l1` (fix length_app'):

  <details><summary>Rocq error</summary>

  ```
  This step does not type-check because an earlier step does not: see the first Rocq error above.
  ```

  </details>
  - ▫️ Let `A : Type`.
  - ▫️ Let `l1 l2 : list A`.
  - ▫️ We prove `length (l1 ++ l2) = length l1 + length l2` by induction on `l1` (list, match):
  - ❌ Case 1 (base): we prove `length ([] ++ l2) = length ([] ++ l2)`.

    <details><summary>Rocq error</summary>

    ```
    This step does not type-check because an earlier step does not: see the first Rocq error above.
    ```

    </details>
    - ❌ By definition of eq (eq_refl), we have `length ([] ++ l2) = length ([] ++ l2)` .*by eapply @eq_refl; eauto*

      <details><summary>Rocq error</summary>

      ```
      File "./cyp_check.v", line 2, characters 21-23:
      Error: The reference l2 was not found in the current environment.
      
      
      ```

      </details>
  - ❌ Case 2 (inductive): we prove `A -> forall l : list A, S (length (l ++ l2)) = S (length l + length l2)`.

    <details><summary>Rocq error</summary>

    ```
    This step does not type-check because an earlier step does not: see the first Rocq error above.
    ```

    </details>
    - ▫️ Let `x : A`.
    - ▫️ Let `l : list A`.
    - ❌ In particular `length (l ++ l2) = length l + length l2`.

      <details><summary>Rocq error</summary>

      ```
      This step does not type-check because an earlier step does not: see the first Rocq error above.
      ```

      </details>
      - ❌ By induction hypothesis (the recursive call length_app') we have `forall (A0 : Type) (l10 l20 : list A0), length (l10 ++ l20) = length l10 + length l20`.

        <details><summary>Rocq error</summary>

        ```
        This step does not type-check because an earlier step does not: see the first Rocq error above.
        ```

        </details>
    - ❌ In particular `length (l ++ l2) = length l + length l2 -> S (length (l ++ l2)) = S (length l + length l2)`.

      <details><summary>Rocq error</summary>

      ```
      This step does not type-check because an earlier step does not: see the first Rocq error above.
      ```

      </details>
      - ❌ Using f_equal we get `forall (A0 B : Type) (f : A0 -> B) (x0 y : A0), x0 = y -> f x0 = f y` .*by exact @f_equal*

        <details><summary>Rocq error</summary>

        ```
        This step does not type-check because an earlier step does not: see the first Rocq error above.
        ```

        </details>
    - ❌ We deduce `S (length (l ++ l2)) = S (length l + length l2)`.

      <details><summary>Rocq error</summary>

      ```
      This step does not type-check because an earlier step does not: see the first Rocq error above.
      ```

      </details>
  - ❌ These cases being exhaustive, we deduce `length (l1 ++ l2) = length l1 + length l2`.

    <details><summary>Rocq error</summary>

    ```
    This step does not type-check because an earlier step does not: see the first Rocq error above.
    ```

    </details>

