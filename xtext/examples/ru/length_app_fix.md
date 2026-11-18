---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: ru
by: tauto | congruence | lia | firstorder | auto
---

# length_app'

Докажем, что `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim}.

- Докажем, что `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim} рекурсией по `l1`{.fact} (fix length_app'):
  - Пусть `A : Type`{.var}.
  - Пусть `l1 l2 : list A`{.var}.
  - Докажем, что `length (l1 ++ l2) = length l1 + length l2`{.fact} индукцией по `l1`{.fact} (list, match):
  - Случай 1 (база): докажем, что `length (nil ++ l2) = length (nil ++ l2)`{.claim}.
    - По определению eq (eq_refl), имеем `length (nil ++ l2) = length (nil ++ l2)`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - Случай 2 (шаг): докажем, что `A -> forall l : list A, S (length (l ++ l2)) = S (length l + length l2)`{.claim}.
    - Пусть `x : A`{.var}.
    - Пусть `l : list A`{.var}.
    - По предположению индукции (рекурсивный вызов length_app') имеем `forall (A0 : Type) (l10 l20 : list A0), length (l10 ++ l20) = length l10 + length l20`{.claim}.
    - Используя f_equal получаем `forall (A0 B : Type) (f : A0 -> B) (x0 y : A0), x0 = y -> f x0 = f y`{.claim} *by Corelib.Init.Logic.f_equal*.
    - Следовательно `S (length (l ++ l2)) = S (length l + length l2)`{.claim} *by congruence*.
  - Эти случаи исчерпывают все возможности, следовательно `length (l1 ++ l2) = length l1 + length l2`{.claim}.
