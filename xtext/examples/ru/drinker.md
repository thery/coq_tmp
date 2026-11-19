---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: ru
by: tauto | congruence | lia | firstorder | auto
---

# drinker

Пусть `A : Set`{.var}. Пусть `P : A -> Prop`{.var}. Пусть `y : A`{.var}. Докажем, что `exists x : A, P x -> forall z : A, P z`{.claim}.

- Применяя *Classical_Prop.classic*{.just}, имеем `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.claim} (o).
  - Элемент `forall z : A, P z` принадлежит `Prop`.
- Докажем, что `exists x : A, P x -> forall z : A, P z` разбором случаев по *o*{.just} (or, match):
  - Случай 1: докажем, что `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
    - Предположим, что `forall z : A, P z`{.hyp} (H).
      - Предположим, что `P y`{.hyp} (_H). По *H*{.just} имеем `forall z : A, P z`{.claim}.
      - Мы доказали `P y -> forall z : A, P z`{.claim}.

      По определению ex (*ex_intro*{.just}) со свидетелем `y`, имеем `exists x : A, P x -> forall z : A, P z`{.claim}.
  - Случай 2: докажем, что `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
    - Предположим, что `~ (forall z : A, P z)`{.hyp} (H).
      - Применяя *Classical_Pred_Type.not_all_ex_not*{.just} к A, P и *H*{.just}, имеем `exists n : A, ~ P n`{.claim} (e).
      - Возвращаясь к определению ex (match) в *e*{.just}, докажем, что `exists x : A, P x -> forall z : A, P z`{.claim}:
        - Выберем произвольно `t : A`{.var}; предположим, что `~ P t`{.hyp} (i).
          - Предположим, что `P t`{.hyp} (h).
            - Применением, с *h*{.just}, имеем `False`{.claim} (f).
              - По *i*{.just} имеем `~ P t`, то есть `P t -> False`{.claim}.

            От противного (False, match), из *f*{.just} можно вывести `forall z : A, P z`{.claim}.
          - Мы доказали `P t -> forall z : A, P z`{.claim}.

          По определению ex (*ex_intro*{.just}) со свидетелем `t`, имеем `exists x : A, P x -> forall z : A, P z`{.claim}.

      Имеем `exists x : A, P x -> forall z : A, P z`{.claim}.

  Имеем `exists x : A, P x -> forall z : A, P z`{.claim} во всех случаях.
