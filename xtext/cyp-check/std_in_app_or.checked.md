<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# in_app_or

✅ Let `A : Type`. Let `l m : list A`. Let `a : A`. We prove `In a (l ++ m) -> In a l \/ In a m`.

- ▫️ To prove `In a (l ++ m) -> In a l \/ In a m` by induction (list, list_ind), we generalise it to `forall l0 : list A, In a (l0 ++ m) -> In a l0 \/ In a m`:
- ✅ Case 1 (base): we prove `In a (nil ++ m) -> In a nil \/ In a m`.
  - ▫️ Assume `In a m` (H).
    - ✅ By definition of or (or_intror), from `In a m` (H) we deduce `False \/ In a m` .*by eapply @or_intror; eauto*
- ✅ Case 2 (inductive): we prove `forall (a0 : A) (l0 : list A), (In a (l0 ++ m) -> In a l0 \/ In a m) -> In a ((a0 :: l0) ++ m) -> In a (a0 :: l0) \/ In a m`.
  - ▫️ Let `a0 : A`.
  - ▫️ Let `l0 : list A`.
  - ▫️ Assume by induction hypothesis `In a (l0 ++ m) -> In a l0 \/ In a m` (IHl).
    - ▫️ Assume `a0 = a \/ In a (l0 ++ m)` (H).
      - ▫️ We prove `(a0 = a \/ In a l0) \/ In a m` by case analysis on `a0 = a \/ In a (l0 ++ m)` (H) (or, or_ind):
      - ✅ Case 2.1: we prove `a0 = a -> (a0 = a \/ In a l0) \/ In a m`.
        - ▫️ Assume `a0 = a` (H0).
          - ✅ By definition of or (or_introl), from `a0 = a` (H0) we deduce `a0 = a \/ In a l0` .*by eapply @or_introl; eauto*
          - ✅ By definition of or (or_introl), we have `(a0 = a \/ In a l0) \/ In a m` .*by eapply @or_introl; eauto*
      - ✅ Case 2.2: we prove `In a (l0 ++ m) -> (a0 = a \/ In a l0) \/ In a m`.
        - ▫️ Assume `In a (l0 ++ m)` (H0).
          - ✅ We deduce `In a l0 \/ In a m` (H1).
            - ✅ By H0 we have `In a (l0 ++ m)`.
            - ✅ By IHl we have `In a (l0 ++ m) -> In a l0 \/ In a m`.
          - ▫️ We prove `(a0 = a \/ In a l0) \/ In a m` by case analysis on `In a l0 \/ In a m` (H1) (or, or_ind):
          - ✅ Case 2.2.1: we prove `In a l0 -> (a0 = a \/ In a l0) \/ In a m`.
            - ▫️ Assume `In a l0` (H10).
              - ✅ By definition of or (or_intror), from `In a l0` (H10) we deduce `a0 = a \/ In a l0` .*by eapply @or_intror; eauto*
              - ✅ By definition of or (or_introl), we have `(a0 = a \/ In a l0) \/ In a m` .*by eapply @or_introl; eauto*
          - ✅ Case 2.2.2: we prove `In a m -> (a0 = a \/ In a l0) \/ In a m`.
            - ▫️ Assume `In a m` (H10).
              - ✅ By definition of or (or_intror), from `In a m` (H10) we deduce `(a0 = a \/ In a l0) \/ In a m` .*by eapply @or_intror; eauto*
          - ✅ We have `(a0 = a \/ In a l0) \/ In a m` in all cases .*by eapply (@or_ind (In a l0) (In a m) ((a0 = a \/ In a l0) \/ In a m)); cbv beta; eauto*
      - ✅ We have `(a0 = a \/ In a l0) \/ In a m` in all cases .*by eapply (@or_ind (a0 = a) (In a (l0 ++ m)) ((a0 = a \/ In a l0) \/ In a m)); cbv beta; eauto*
- ✅ These cases being exhaustive, we deduce `forall l0 : list A, In a (l0 ++ m) -> In a l0 \/ In a m` .*by eapply (@list_ind (A) (fun l0 : list A => In a (l0 ++ m) -> In a l0 \/ In a m)); cbv beta; eauto*
- ❌ In particular `In a (l ++ m) -> In a l \/ In a m`.

  <details><summary>not proved</summary>

  ```
  1 goal
    
    A : Type
    l, m : list A
    a : A
    H : In a ([] ++ m) -> In a [] \/ In a m
    H0 :
      forall (a0 : A) (l0 : list A),
      (In a (l0 ++ m) -> In a l0 \/ In a m) ->
      In a ((a0 :: l0) ++ m) -> In a (a0 :: l0) \/ In a m
    H1 : forall l0 : list A, In a (l0 ++ m) -> In a l0 \/ In a m
    H2 : In a (l ++ m)
    ============================
    In a l \/ In a m
  
  File "./cyp_ko_19.v", line 4, characters 0-168:
  Error: No applicable tactic.
  ```

  </details>

