---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
lang: ru
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# add_0_r'

✅ Пусть `n : nat`{.var}. Докажем, что `n + 0 = n`{.claim}.

- ✅ Докажем, что `n + 0 = n` индукцией по *n*{.just} (*nat*{.just}, *induction*{.just}):
  - ✅ Случай 1 (база): докажем, что `0 = 0`{.claim}.
    - ✅ По определению eq (*eq_refl*{.just}), имеем `0 = 0`{.claim}.
  - ✅ Случай 2 (шаг): докажем, что `forall m : nat, m + 0 = m -> S m + 0 = S m`{.claim}.
    - ✅ Выберем произвольно `m : nat`{.var}; предположим, что по предположению индукции `m + 0 = m`{.hyp} (IH).
      - ✅ По определению eq (*eq_refl*{.just}), имеем `S m = S m`{.claim}.
      - ✅ По *IH*{.just} имеем `m + 0 = m`{.claim}.

      Переписывая с помощью `m + 0 = m`{.fact} справа налево (eq_ind_r), получаем `S (m + 0) = S m`{.claim}.

  Эти случаи исчерпывают все возможности, следовательно `n + 0 = n`{.claim}.
