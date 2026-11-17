<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# Nat.pred_succ

✅ Let `n : nat`. We prove `Nat.pred (S n) = n`.

- ✅ By definition of eq (eq_refl), we have `n = n` , that is `Nat.pred (S n) = n`.*by eapply @eq_refl; eauto*

