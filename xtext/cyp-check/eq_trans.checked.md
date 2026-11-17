<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List. Import ListNotations. Require Import XText.inductive. -->

# eq_trans'

✅ Let `a b c : nat`. Assume `a = b` (H1) and `b = c` (H2). We prove `a = c`.

- ✅ By H2 we have `b = c`.
- ✅ By H1 we have `a = b`.
- ✅ Rewriting with `a = b` from right to left (eq_ind_r), we get `a = c`.

