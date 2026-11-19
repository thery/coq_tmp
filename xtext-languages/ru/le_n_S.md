---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: ru
by: tauto | congruence | lia | firstorder | auto
---

# le_n_S'

Пусть `n m : nat`{.var}. Предположим, что `n <= m`{.hyp} (H). Докажем, что `S n <= S m`{.claim}.

- Докажем, что `S n <= S m`{.fact} индукцией по `n <= m`{.fact} (H) (le, le_ind):
- Случай 1 (база): докажем, что `S n <= S n`{.claim}.
  - По определению le (le_n), имеем `S n <= S n`{.claim} *by Corelib.Init.Peano.le_n*.
- Случай 2 (шаг): докажем, что `forall m0 : nat, n <= m0 -> S n <= S m0 -> S n <= S (S m0)`{.claim}.
  - Выберем произвольно `m0 : nat`{.var}; предположим, что `n <= m0`{.hyp} (H0) и по предположению индукции `S n <= S m0`{.hyp} (IH).
    - По определению le (le_S) со свидетелем `S m0`{.fact}, из `S n <= S m0`{.fact} (IH) следовательно `S n <= S (S m0)`{.claim} *by Corelib.Init.Peano.le_S*.
- Имеем `S n <= S m`{.claim} во всех случаях.
