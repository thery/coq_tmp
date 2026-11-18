---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: la
by: tauto | congruence | lia | firstorder | auto
---

# length_app'

Ostendamus `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim}.

- Ostendamus `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim} per recursionem in `l1`{.fact} (fix length_app'):
  - Sit `A : Type`{.var}.
  - Sint `l1 l2 : list A`{.var}.
  - Ostendamus `length (l1 ++ l2) = length l1 + length l2`{.fact} per inductionem in `l1`{.fact} (list, match):
  - Casus 1 (basis): ostendamus `length (nil ++ l2) = length (nil ++ l2)`{.claim}.
    - Ex definitione eq (eq_refl), habemus `length (nil ++ l2) = length (nil ++ l2)`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - Casus 2 (gradus): ostendamus `A -> forall l : list A, S (length (l ++ l2)) = S (length l + length l2)`{.claim}.
    - Sit `x : A`{.var}.
    - Sit `l : list A`{.var}.
    - Per hypothesim inductionis (vocatio recursiva length_app') habemus `forall (A0 : Type) (l10 l20 : list A0), length (l10 ++ l20) = length l10 + length l20`{.claim}.
    - Adhibentes f_equal obtinemus `forall (A0 B : Type) (f : A0 -> B) (x0 y : A0), x0 = y -> f x0 = f y`{.claim} *by Corelib.Init.Logic.f_equal*.
    - Unde sequitur `S (length (l ++ l2)) = S (length l + length l2)`{.claim} *by congruence*.
  - His casibus exhaustis, unde sequitur `length (l1 ++ l2) = length l1 + length l2`{.claim}.
