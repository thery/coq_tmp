---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: ru
by: tauto | congruence | lia | firstorder | auto
---

# drinker

Пусть `A : Set`{.var}. Пусть `P : A -> Prop`{.var}. Пусть `y : A`{.var}. Докажем, что `exists x : A, P x -> forall z : A, P z`{.claim}.

- Применяя classic, имеем `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.claim} (o).
  - Элемент `forall z : A, P z`{.fact} принадлежит `Prop`{.fact}.
- Докажем, что `exists x : A, P x -> forall z : A, P z`{.fact} разбором случаев по `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.fact} (o) (or, match):
- Случай 1: докажем, что `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - Предположим, что `forall z : A, P z`{.hyp} (H).
    - Предположим, что `P y`{.hyp} (_H).
      - По H имеем `forall z : A, P z`{.claim}.
    - Мы доказали `P y -> forall z : A, P z`{.claim}.
    - По определению ex (ex_intro) со свидетелем `y`{.fact}, имеем `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- Случай 2: докажем, что `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - Предположим, что `~ (forall z : A, P z)`{.hyp} (H).
    - Применяя not_all_ex_not к A, P и H, имеем `exists n : A, ~ P n`{.claim} (e).
    - Возвращаясь к определению ex (match) в `exists n : A, ~ P n`{.fact} (e), докажем, что `exists x : A, P x -> forall z : A, P z`{.claim}:
      - Выберем произвольно `t : A`{.var}; предположим, что `~ P t`{.hyp} (i).
        - Предположим, что `P t`{.hyp} (h).
          - Применением, с h, имеем `False`{.claim} (f).
            - По i имеем `~ P t`{.claim}, то есть `P t -> False`{.fact}.
          - От противного (False, match), из `False`{.fact} (f) можно вывести `forall z : A, P z`{.claim}.
        - Мы доказали `P t -> forall z : A, P z`{.claim}.
        - По определению ex (ex_intro) со свидетелем `t`{.fact}, имеем `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- Имеем `exists x : A, P x -> forall z : A, P z`{.claim} во всех случаях.
