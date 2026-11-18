---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
lang: ru
by: tauto | congruence | lia | firstorder | auto
---

# add_0_r'

Пусть `n : nat`{.var}. Докажем, что `n + 0 = n`{.claim}.

- Чтобы доказать `n + 0 = n`{.fact} индукцией (nat, nat_ind), обобщим до `forall n0 : nat, n0 + 0 = n0`{.fact}:
- Случай 1 (база): докажем, что `0 = 0`{.claim}.
  - По определению eq (eq_refl), имеем `0 = 0`{.claim} *by Corelib.Init.Logic.eq_refl*.
- Случай 2 (шаг): докажем, что `forall m : nat, m + 0 = m -> S m + 0 = S m`{.claim}.
  - Рассмотрим произвольное `m : nat`{.var}.
    - Предположим, что по предположению индукции `m + 0 = m`{.hyp} (IH).
      - По определению eq (eq_refl), имеем `S m = S m`{.claim} *by Corelib.Init.Logic.eq_refl*.
      - По IH имеем `m + 0 = m`{.claim}.
      - Переписывая с помощью `m + 0 = m`{.fact} справа налево (eq_ind_r), получаем `S (m + 0) = S m`{.claim}.
- Эти случаи исчерпывают все возможности, следовательно `forall n0 : nat, n0 + 0 = n0`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
- В частности `n + 0 = n`{.claim}.
