---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: la
by: tauto | congruence | lia | firstorder | auto
---

# length_app'

✅ Ostendamus `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim}.

- ✅ Ostendamus `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim} per recursionem in `l1` (fix length_app'):
  - ✅ Sit `A : Type`{.var} et `l1 l2 : list A`{.var}. Ostendamus `length (l1 ++ l2) = length l1 + length l2` per inductionem in *l1*{.just} (*list*{.just}, *induction*{.just}):
    - ✅ Casus 1 (basis): ostendamus `length (nil ++ l2) = length (nil ++ l2)`{.claim}.
      - ✅ Ex definitione eq (*eq_refl*{.just}), habemus `length (nil ++ l2) = length (nil ++ l2)`{.claim}.
    - ✅ Casus 2 (gradus): ostendamus `A -> forall l : list A, S (length (l ++ l2)) = S (length l + length l2)`{.claim}.
      - ✅ Sit `x : A`{.var} et `l : list A`{.var}.
        - ▫️ Elementum `nat` pertinet ad `Type`.
        - ▫️ Elementum `nat` pertinet ad `Type`.
        - ▫️ Elementum `S` pertinet ad `nat -> nat`.
        - ▫️ Elementum `length (l ++ l2)` pertinet ad `nat`.
        - ▫️ Elementum `length l + length l2` pertinet ad `nat`.
        - ✅ Speciatim `length (l ++ l2) = length l + length l2`{.claim}.
          - ✅ Per hypothesim inductionis (vocatio recursiva length_app') habemus `forall (A0 : Type) (l10 l20 : list A0), length (l10 ++ l20) = length l10 + length l20`{.claim}.

        Applicando *f_equal*{.just}, habemus `S (length (l ++ l2)) = S (length l + length l2)`{.claim}.

    His casibus exhaustis, unde sequitur `length (l1 ++ l2) = length l1 + length l2`{.claim}.
