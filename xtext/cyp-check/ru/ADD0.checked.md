---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: ru
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

✅ Пусть `m : nat`{.var}. Докажем, что `m + 0 = m`{.claim}.

- ✅ Докажем, что `m + 0 = m` индукцией по `m` (nat, *nat_ind*{.just}):
  - ✅ Случай 1 (база): докажем, что `0 + 0 = 0 + 0`{.claim}.
    - ✅ По определению eq (*eq_refl*{.just}), имеем `0 + 0 = 0 + 0`{.claim}.
  - ✅ Случай 2 (шаг): докажем, что `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
    - ✅ Выберем произвольно `m0 : nat`{.var}; предположим, что по предположению индукции `m0 + 0 = m0`{.hyp} (IH).
      - ▫️ Элемент `nat` принадлежит `Type`.
      - ▫️ Элемент `nat` принадлежит `Type`.
      - ▫️ Элемент `S` принадлежит `nat -> nat`.
      - ▫️ Элемент `m0 + 0` принадлежит `nat`.
      - ✅ По *IH*{.just} имеем `m0 + 0 = m0`{.claim}.

      Применяя *f_equal*{.just}, имеем `S (m0 + 0) = S m0`{.claim}.

  Эти случаи исчерпывают все возможности, следовательно `m + 0 = m`{.claim}.
