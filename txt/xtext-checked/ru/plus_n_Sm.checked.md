---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: ru
by: tauto | congruence | lia | firstorder | auto
---

# plus_n_Sm'

✅ Пусть `n m : nat`{.var}. Докажем, что `S (n + m) = n + S m`{.claim}.

- ▫️ Докажем, что `S (n + m) = n + S m`{.fact} индукцией по `n`{.fact} (nat, nat_ind):
- ✅ Случай 1 (база): докажем, что `0 + S m = 0 + S m`{.claim}.
  - ✅ По определению eq (eq_refl), имеем `0 + S m = 0 + S m`{.claim} *by Corelib.Init.Logic.eq_refl*.
- ✅ Случай 2 (шаг): докажем, что `forall n0 : nat, S (n0 + m) = n0 + S m -> S (S n0 + m) = S n0 + S m`{.claim}.
  - ▫️ Выберем произвольно `n0 : nat`{.var}; предположим, что по предположению индукции `S (n0 + m) = n0 + S m`{.hyp} (IH).
    - ✅ По определению eq (eq_refl), имеем `S (n0 + S m) = S (n0 + S m)`{.claim} *by Corelib.Init.Logic.eq_refl*.
    - ✅ По IH имеем `S (n0 + m) = n0 + S m`{.claim}.
    - ✅ Переписывая с помощью `S (n0 + m) = n0 + S m`{.fact} справа налево (eq_ind_r), получаем `S (S (n0 + m)) = S (n0 + S m)`{.claim}.
- ✅ Эти случаи исчерпывают все возможности, следовательно `S (n + m) = n + S m`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
