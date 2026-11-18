---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: ru
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

Пусть `m : nat`{.var}. Докажем, что `m + 0 = m`{.claim}.

- Чтобы доказать `m + 0 = m`{.fact} индукцией (nat, nat_ind), обобщим до `forall n : nat, n + 0 = n`{.fact}:
- Случай 1 (база): докажем, что `0 + 0 = 0 + 0`{.claim}.
  - По определению eq (eq_refl), имеем `0 + 0 = 0 + 0`{.claim} *by Corelib.Init.Logic.eq_refl*.
- Случай 2 (шаг): докажем, что `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
  - Рассмотрим произвольное `m0 : nat`{.var}.
    - Предположим, что по предположению индукции `m0 + 0 = m0`{.hyp} (IH).
      - По IH имеем `m0 + 0 = m0`{.claim}.
      - Используя f_equal получаем `forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y`{.claim} *by Corelib.Init.Logic.f_equal*.
      - Следовательно `S (m0 + 0) = S m0`{.claim}.
- Эти случаи исчерпывают все возможности, следовательно `forall n : nat, n + 0 = n`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
- В частности `m + 0 = m`{.claim}.
