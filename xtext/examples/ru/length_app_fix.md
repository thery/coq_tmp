---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: ru
by: tauto | congruence | lia | firstorder | auto
---

# length_app'

Докажем, что `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim}.

- Докажем, что `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim} рекурсией по `l1`{.fact} (fix length_app'):
  - Пусть `A : Type`{.var} и `l1 l2 : list A`{.var}.
    - Докажем, что `length (l1 ++ l2) = length l1 + length l2`{.fact} индукцией по `l1`{.fact} (list, match):
    - Случай 1 (база): докажем, что `length (nil ++ l2) = length (nil ++ l2)`{.claim}.
      - По определению eq (eq_refl), имеем `length (nil ++ l2) = length (nil ++ l2)`{.claim} *by Corelib.Init.Logic.eq_refl*.
    - Случай 2 (шаг): докажем, что `A -> forall l : list A, S (length (l ++ l2)) = S (length l + length l2)`{.claim}.
      - Пусть `x : A`{.var} и `l : list A`{.var}.
        - Элемент `nat`{.fact} принадлежит `Type`{.fact}.
        - Элемент `nat`{.fact} принадлежит `Type`{.fact}.
        - Элемент `S`{.fact} принадлежит `nat -> nat`{.fact}.
        - Элемент `length (l ++ l2)`{.fact} принадлежит `nat`{.fact}.
        - Элемент `length l + length l2`{.fact} принадлежит `nat`{.fact}.
        - В частности `length (l ++ l2) = length l + length l2`{.claim}.
          - По предположению индукции (рекурсивный вызов length_app') имеем `forall (A0 : Type) (l10 l20 : list A0), length (l10 ++ l20) = length l10 + length l20`{.claim}.
        - Применяя f_equal, имеем `S (length (l ++ l2)) = S (length l + length l2)`{.claim}.
    - Эти случаи исчерпывают все возможности, следовательно `length (l1 ++ l2) = length l1 + length l2`{.claim}.
