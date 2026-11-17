<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas. -->

# ex_forall

✅ Let `P : nat -> nat -> Prop`. Assume `exists x : nat, forall y : nat, P x y` (H0). We prove `forall y : nat, exists x : nat, P x y`.

- ✅ Going back to the definition of ex (match) in `exists x : nat, forall y : nat, P x y` (H0), we prove `forall y : nat, exists x : nat, P x y`:
  - ▫️ Let us consider an arbitrary `x : nat`.
    - ▫️ Assume `forall y : nat, P x y` (H).
      - ▫️ Let us consider an arbitrary `y : nat`.
        - ✅ By H we have `forall y0 : nat, P x y0`.
        - ✅ In particular `P x y`.
        - ✅ By definition of ex (ex_intro) with witness `x`, we have `exists x0 : nat, P x0 y` .*by eapply @ex_intro; eauto*

