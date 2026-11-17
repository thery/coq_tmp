<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# in_or_app

✅ Let `A : Type`. Let `l m : list A`. Let `a : A`. We prove `In a l \/ In a m -> In a (l ++ m)`.

- ▫️ To prove `In a l \/ In a m -> In a (l ++ m)` by induction (list, list_ind), we generalise it to `forall l0 : list A, In a l0 \/ In a m -> In a (l0 ++ m)`:
- ✅ Case 1 (base): we prove `In a nil \/ In a m -> In a (nil ++ m)`.
  - ▫️ Assume `False \/ In a m` (H).
    - ▫️ We prove `In a m` by case analysis on `False \/ In a m` (H) (or, or_ind):
    - ✅ Case 1.1: we prove `False -> In a m`.
      - ▫️ Assume `False` (H0).
        - ✅ By contradiction (False, False_ind), from `False` (H0) we can deduce `In a m`.
    - ✅ Case 1.2: we prove `In a m -> In a m`.
      - ▫️ Assume `In a m` (H0).
        - ✅ By H0 we have `In a m`.
    - ✅ We have `In a m` in all cases .*by eapply (@or_ind (False) (In a m) (In a m)); cbv beta; eauto*
- ✅ Case 2 (inductive): we prove `forall (a0 : A) (l0 : list A), (In a l0 \/ In a m -> In a (l0 ++ m)) -> In a (a0 :: l0) \/ In a m -> In a ((a0 :: l0) ++ m)`.
  - ▫️ Let `a0 : A`.
  - ▫️ Let `l0 : list A`.
  - ▫️ Assume by induction hypothesis `In a l0 \/ In a m -> In a (l0 ++ m)` (IHl).
    - ✅ We have `(a0 = a \/ In a l0) \/ In a m -> a0 = a \/ In a (l0 ++ m)` .*by tauto*
- ✅ These cases being exhaustive, we deduce `forall l0 : list A, In a l0 \/ In a m -> In a (l0 ++ m)` .*by eapply (@list_ind (A) (fun l0 : list A => In a l0 \/ In a m -> In a (l0 ++ m))); cbv beta; eauto*
- ✅ In particular `In a l \/ In a m -> In a (l ++ m)`.

