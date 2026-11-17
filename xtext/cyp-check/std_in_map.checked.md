<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# in_map

✅ Let `A B : Type`. Let `f : A -> B`. Let `l : list A`. We prove `forall x : A, In x l -> In (f x) (map f l)`.

- ▫️ To prove `forall x : A, In x l -> In (f x) (map f l)` by induction (list, list_ind), we generalise it to `forall (l0 : list A) (x : A), In x l0 -> In (f x) (map f l0)`:
- ✅ Case 1 (base): we prove `forall x : A, In x nil -> In x nil`.
  - ▫️ Let `x : A`.
  - ▫️ Assume `In x nil` (H).
    - ✅ By H we have `In x nil`.
- ✅ Case 2 (inductive): we prove `forall (a : A) (l0 : list A), (forall x : A, In x l0 -> In (f x) (map f l0)) -> forall x : A, In x (a :: l0) -> In (f x) (map f (a :: l0))`.
  - ▫️ Let `a : A`.
  - ▫️ Let `l0 : list A`.
  - ▫️ Assume by induction hypothesis `forall x : A, In x l0 -> In (f x) (map f l0)` (IHl).
    - ▫️ Let `x : A`.
    - ▫️ Assume `In x (a :: l0)` (H).
      - ▫️ We prove `In (f x) (map f (a :: l0))` by case analysis on `In x (a :: l0)` (H) (or, or_ind):
      - ✅ Case 2.1: we prove `a = x -> f a = f x \/ In (f x) (map f l0)`.
        - ▫️ Assume `a = x` (H0).
          - ✅ By definition of eq (eq_refl), we have `f x = f x` .*by eapply @eq_refl; eauto*
          - ✅ By H0 we have `a = x`.
          - ✅ Rewriting with `a = x` from right to left (eq_ind_r), we get `f a = f x`.
          - ✅ By definition of or (or_introl), we have `f a = f x \/ In (f x) (map f l0)` .*by eapply @or_introl; eauto*
      - ✅ Case 2.2: we prove `In x l0 -> f a = f x \/ In (f x) (map f l0)`.
        - ▫️ Assume `In x l0` (H0).
          - ✅ By IHl we have `forall x0 : A, In x0 l0 -> In (f x0) (map f l0)`.
          - ✅ We have proved `(In x l0 -> In (f x) (map f l0)) -> In (f x) (map f l0)`.
            - ▫️ Assume `In x l0 -> In (f x) (map f l0)` (H00).
              - ✅ By H0 we have `In x l0`.
              - ✅ By H00 we have `In x l0 -> In (f x) (map f l0)`.
              - ✅ We have proved `In (f x) (map f l0) -> In (f x) (map f l0)`.
                - ▫️ Assume `In (f x) (map f l0)` (H01).
                  - ✅ By H01 we have `In (f x) (map f l0)`.
              - ✅ We deduce `In (f x) (map f l0)` .*by tauto*
          - ✅ We deduce `In (f x) (map f l0)` .*by firstorder*
          - ✅ By definition of or (or_intror), we have `f a = f x \/ In (f x) (map f l0)` .*by eapply @or_intror; eauto*
      - ✅ We have `In (f x) (map f (a :: l0))` in all cases .*by eapply (@or_ind (a = x) (In x l0) (In (f x) (map f (a :: l0)))); cbv beta; eauto*
- ✅ These cases being exhaustive, we deduce `forall (l0 : list A) (x : A), In x l0 -> In (f x) (map f l0)` .*by eapply (@list_ind (A) (fun l0 : list A => forall x : A, In x l0 -> In (f x) (map f l0))); cbv beta; eauto*
- ✅ In particular `forall x : A, In x l -> In (f x) (map f l)`.

