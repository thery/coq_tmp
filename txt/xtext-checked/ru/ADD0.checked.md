---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: ru
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

✅ Пусть `m : nat`{.var}. Докажем, что `m + 0 = m`{.claim}.

- ▫️ Докажем, что `m + 0 = m`{.fact} индукцией по `m`{.fact} (nat, nat_ind):
- ✅ Случай 1 (база): докажем, что `0 + 0 = 0 + 0`{.claim}.
  - ✅ По определению eq (eq_refl), имеем `0 + 0 = 0 + 0`{.claim} *by Corelib.Init.Logic.eq_refl*.
- ✅ Случай 2 (шаг): докажем, что `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
  - ▫️ Выберем произвольно `m0 : nat`{.var}; предположим, что по предположению индукции `m0 + 0 = m0`{.hyp} (IH).
    - ▫️ Элемент `nat`{.fact} принадлежит `Type`{.fact}.
    - ▫️ Элемент `nat`{.fact} принадлежит `Type`{.fact}.
    - ▫️ Элемент `S`{.fact} принадлежит `nat -> nat`{.fact}.
    - ▫️ Элемент `m0 + 0`{.fact} принадлежит `nat`{.fact}.
    - ▫️ Элемент `m0`{.fact} принадлежит `nat`{.fact}.
    - ✅ По IH имеем `m0 + 0 = m0`{.claim}.
    - ✅ Применяя f_equal, имеем `S (m0 + 0) = S m0`{.claim}.
- ✅ Эти случаи исчерпывают все возможности, следовательно `m + 0 = m`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
