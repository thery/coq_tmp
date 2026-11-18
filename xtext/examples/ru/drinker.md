---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: ru
by: tauto | congruence | lia | firstorder | auto
---

# drinker

Пусть `A : Set`{.var}. Пусть `P : A -> Prop`{.var}. Пусть `y : A`{.var}. Докажем, что `exists x : A, P x -> forall z : A, P z`{.claim}.

- В частности `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.claim} (o).
  - Используя classic получаем `forall P0 : Prop, P0 \/ ~ P0`{.claim} *by Stdlib.Logic.Classical_Prop.classic*.
- Докажем, что `exists x : A, P x -> forall z : A, P z`{.fact} разбором случаев по `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.fact} (o) (or, match):
- Случай 1: докажем, что `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - Предположим, что `forall z : A, P z`{.hyp} (H).
    - Предположим, что `P y`{.hyp} (_H).
      - По H имеем `forall z : A, P z`{.claim}.
    - Мы доказали `P y -> forall z : A, P z`{.claim}.
    - По определению ex (ex_intro) со свидетелем `y`{.fact}, имеем `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- Случай 2: докажем, что `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - Предположим, что `~ (forall z : A, P z)`{.hyp} (H).
    - Следовательно `exists n : A, ~ P n`{.claim} (e).
      - По H имеем `~ (forall z : A, P z)`{.claim}.
      - Используя not_all_ex_not получаем `forall (U : Type) (P0 : U -> Prop), ~ (forall n : U, P0 n) -> exists n : U, ~ P0 n`{.claim} *by Stdlib.Logic.Classical_Pred_Type.not_all_ex_not*.
    - Возвращаясь к определению ex (match) в `exists n : A, ~ P n`{.fact} (e), докажем, что `exists x : A, P x -> forall z : A, P z`{.claim}:
      - Рассмотрим произвольное `t : A`{.var}.
        - Предположим, что `~ P t`{.hyp} (i).
          - Предположим, что `P t`{.hyp} (h).
            - Следовательно `False`{.claim} (f).
              - По h имеем `P t`{.claim}.
              - По i имеем `~ P t`{.claim}, то есть `P t -> False`{.fact}.
            - От противного (False, match), из `False`{.fact} (f) можно вывести `forall z : A, P z`{.claim}.
          - Мы доказали `P t -> forall z : A, P z`{.claim}.
          - По определению ex (ex_intro) со свидетелем `t`{.fact}, имеем `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- Имеем `exists x : A, P x -> forall z : A, P z`{.claim} во всех случаях.
