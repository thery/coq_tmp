<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# app_comm_cons

✅ Let `A : Type`. Let `x y : list A`. Let `a : A`. We prove `(a :: x) ++ y = (a :: x) ++ y`.

- ✅ By definition of eq (eq_refl), we have `(a :: x) ++ y = (a :: x) ++ y` .*by eapply @eq_refl; eauto*

