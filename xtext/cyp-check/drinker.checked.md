<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper. -->

# drinker

✅ Let `A : Set`. Let `P : A -> Prop`. Let `y : A`. We prove `exists x : A, P x -> forall z : A, P z`.

- ✅ In particular `(forall z : A, P z) \/ ~ (forall z : A, P z)` (o).
  - ✅ Using classic we get `forall P0 : Prop, P0 \/ ~ P0` .*by exact @Stdlib.Logic.Classical_Prop.classic*
- ▫️ We prove `exists x : A, P x -> forall z : A, P z` by case analysis on `(forall z : A, P z) \/ ~ (forall z : A, P z)` (o) (or, match):
- ✅ Case 1: we prove `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`.
  - ▫️ Assume `forall z : A, P z` (H).
    - ▫️ Assume `P y` (_H).
      - ✅ By H we have `forall z : A, P z`.
    - ✅ We have proved `P y -> forall z : A, P z`.
    - ✅ By definition of ex (ex_intro) with witness `y`, we have `exists x : A, P x -> forall z : A, P z` .*by eapply @ex_intro; eauto*
- ✅ Case 2: we prove `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`.
  - ▫️ Assume `~ (forall z : A, P z)` (H).
    - ✅ We deduce `exists n : A, ~ P n` (e).
      - ✅ By H we have `~ (forall z : A, P z)`.
      - ✅ Using not_all_ex_not we get `forall (U : Type) (P0 : U -> Prop), ~ (forall n : U, P0 n) -> exists n : U, ~ P0 n` .*by exact @Stdlib.Logic.Classical_Pred_Type.not_all_ex_not*
    - ✅ Going back to the definition of ex (match) in `exists n : A, ~ P n` (e), we prove `exists x : A, P x -> forall z : A, P z`:
      - ▫️ Let us consider an arbitrary `t : A`.
        - ▫️ Assume `~ P t` (i).
          - ▫️ Assume `P t` (h).
            - ✅ We deduce `False` (f).
              - ✅ By h we have `P t`.
              - ✅ By i we have `~ P t`, that is `P t -> False`.
            - ✅ By contradiction (False, match), from `False` (f) we can deduce `forall z : A, P z`.
          - ✅ We have proved `P t -> forall z : A, P z`.
          - ✅ By definition of ex (ex_intro) with witness `t`, we have `exists x : A, P x -> forall z : A, P z` .*by eapply @ex_intro; eauto*
- ✅ We have `exists x : A, P x -> forall z : A, P z` in all cases.

