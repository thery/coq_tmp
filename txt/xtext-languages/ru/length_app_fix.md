---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: ru
by: tauto | congruence | lia | firstorder | auto
---

# length_app'

Докажем, что `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim}.

- Докажем, что `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim} рекурсией по `l1` (fix length_app'):
  - Пусть `A : Type`{.var} и `l1 l2 : list A`{.var}. Докажем, что `length (l1 ++ l2) = length l1 + length l2` индукцией по `l1` (list, match):
    - Случай 1 (база): докажем, что `length (nil ++ l2) = length (nil ++ l2)`{.claim}.
      - По определению eq (*eq_refl*{.just}), имеем `length (nil ++ l2) = length (nil ++ l2)`{.claim}.
    - Случай 2 (шаг): докажем, что `A -> forall l : list A, S (length (l ++ l2)) = S (length l + length l2)`{.claim}.
      - Пусть `x : A`{.var} и `l : list A`{.var}.
        - Элемент `nat` принадлежит `Type`.
        - Элемент `nat` принадлежит `Type`.
        - Элемент `S` принадлежит `nat -> nat`.
        - Элемент `length (l ++ l2)` принадлежит `nat`.
        - Элемент `length l + length l2` принадлежит `nat`.
        - В частности `length (l ++ l2) = length l + length l2`{.claim}.
          - По предположению индукции (рекурсивный вызов length_app') имеем `forall (A0 : Type) (l10 l20 : list A0), length (l10 ++ l20) = length l10 + length l20`{.claim}.

        Применяя *f_equal*{.just}, имеем `S (length (l ++ l2)) = S (length l + length l2)`{.claim}.

    Эти случаи исчерпывают все возможности, следовательно `length (l1 ++ l2) = length l1 + length l2`{.claim}.
