<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# length_app

❌ Let `A : Type`. Let `l : list A`. We prove `forall l' : list A, length (l ++ l') = length l + length l'`.

<details><summary>Rocq error</summary>

```
This step does not type-check because an earlier step does not: see the first Rocq error above.
```

</details>

- ▫️ To prove `forall l' : list A, length (l ++ l') = length l + length l'` by induction (list, list_ind), we generalise it to `forall l0 l' : list A, length (l0 ++ l') = length l0 + length l'`:
- ❌ Case 1 (base): we prove `forall l' : list A, length (nil ++ l') = length nil + length l'`.

  <details><summary>Rocq error</summary>

  ```
  CYP-OK 1
  File "./cyp_check.v", line 6, characters 133-139:
  Error: Cannot infer the implicit parameter A of length whose type is 
  "Type" in environment:
  A : Type
  l, l' : list A
  
  
  ```

  </details>
  - ▫️ Let `l' : list A`.
  - ✅ By definition of eq (eq_refl), we have `length l' = length l'` .*by eapply @eq_refl; eauto*
- ❌ Case 2 (inductive): we prove `forall (a : A) (l0 : list A), (forall l' : list A, length (l0 ++ l') = length l0 + length l') -> forall l' : list A, length ((a :: l0) ++ l') = length (a :: l0) + length l'`.

  <details><summary>Rocq error</summary>

  ```
  This step does not type-check because an earlier step does not: see the first Rocq error above.
  ```

  </details>
  - ▫️ Let `a : A`.
  - ▫️ Let `l0 : list A`.
  - ▫️ Assume by induction hypothesis `forall l' : list A, length (l0 ++ l') = length l0 + length l'` (IHl).
    - ▫️ Let `l' : list A`.
    - ❌ In particular `length (l0 ++ l') = length l0 + length l'`.

      <details><summary>Rocq error</summary>

      ```
      This step does not type-check because an earlier step does not: see the first Rocq error above.
      ```

      </details>
      - ❌ By IHl we have `forall l'0 : list A, length (l0 ++ l'0) = length l0 + length l'0`.

        <details><summary>Rocq error</summary>

        ```
        CYP-OK 1
        File "./cyp_check.v", line 6, characters 116-122:
        Error: Cannot infer the implicit parameter A of length whose type is 
        "Type" in environment:
        A : Type
        l : list A
        a : A
        l0, l'0, l' : list A
        
        
        ```

        </details>
    - ❌ In particular `length (l0 ++ l') = length l0 + length l' -> S (length (l0 ++ l')) = S (length l0 + length l')`.

      <details><summary>Rocq error</summary>

      ```
      This step does not type-check because an earlier step does not: see the first Rocq error above.
      ```

      </details>
      - ❌ Using f_equal_nat we get `forall (B : Type) (f : nat -> B) (x y : nat), x = y -> f x = f y` .*by exact @f_equal_nat*

        <details><summary>Rocq error</summary>

        ```
        This step does not type-check because an earlier step does not: see the first Rocq error above.
        ```

        </details>
    - ❌ We deduce `S (length (l0 ++ l')) = S (length l0 + length l')`.

      <details><summary>Rocq error</summary>

      ```
      This step does not type-check because an earlier step does not: see the first Rocq error above.
      ```

      </details>
- ❌ These cases being exhaustive, we deduce `forall l0 l' : list A, length (l0 ++ l') = length l0 + length l'` .*by eapply (@list_ind (A) (fun l0 : list A => forall l' : list A, length (l0 ++ l') = length l0 + length l')); cbv beta; eauto*

  <details><summary>Rocq error</summary>

  ```
  This step does not type-check because an earlier step does not: see the first Rocq error above.
  ```

  </details>
- ❌ In particular `forall l' : list A, length (l ++ l') = length l + length l'`.

  <details><summary>Rocq error</summary>

  ```
  This step does not type-check because an earlier step does not: see the first Rocq error above.
  ```

  </details>

