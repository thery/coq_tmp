<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive. -->

# length_app'

✅ We prove `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`.

- ✅ We prove `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2` by recursion on `l1` (fix length_app'):
  - ▫️ Let `A : Type`.
  - ▫️ Let `l1 l2 : list A`.
  - ▫️ We prove `length (l1 ++ l2) = length l1 + length l2` by induction on `l1` (list, match):
  - ✅ Case 1 (base): we prove `length ([] ++ l2) = length ([] ++ l2)`.
    - ✅ By definition of eq (eq_refl), we have `length ([] ++ l2) = length ([] ++ l2)` .*by eapply @eq_refl; eauto*
  - ✅ Case 2 (inductive): we prove `A -> forall l : list A, S (length (l ++ l2)) = S (length l + length l2)`.
    - ▫️ Let `x : A`.
    - ▫️ Let `l : list A`.
    - ❌ By induction hypothesis (the recursive call length_app') we have `forall (A0 : Type) (l10 l20 : list A0), length (l10 ++ l20) = length l10 + length l20`.

      <details><summary>not proved</summary>

      ```
      1 goal
        
        A : Type
        l1, l2 : list A
        x : A
        l : list A
        H : length ([] ++ l2) = length ([] ++ l2)
        A0 : Type
        l10, l20 : list A0
        ============================
        length (l10 ++ l20) = length l10 + length l20
      
      File "./cyp_ko_3.v", line 4, characters 0-168:
      Error: No applicable tactic.
      ```

      </details>
    - ✅ Using f_equal we get `forall (A0 B : Type) (f : A0 -> B) (x0 y : A0), x0 = y -> f x0 = f y` .*by exact @Corelib.Init.Logic.f_equal*
    - ✅ We deduce `S (length (l ++ l2)) = S (length l + length l2)` .*by congruence*
  - ✅ These cases being exhaustive, we deduce `length (l1 ++ l2) = length l1 + length l2` .*by destruct l1; cbn; eauto*

