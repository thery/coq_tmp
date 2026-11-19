---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: ar
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# length_app'

سنثبت أن `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim}.

- سنثبت أن `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim} بالتكرار على `l1` (fix length_app'):
  - ليكن `A : Type`{.var} و `l1 l2 : list A`{.var}. سنثبت أن `length (l1 ++ l2) = length l1 + length l2` بالاستقراء على `l1` (list, match):
    - الحالة 1 (الأساس): سنثبت أن `length (nil ++ l2) = length (nil ++ l2)`{.claim}.
      - حسب تعريف eq (*eq_refl*{.just}), لدينا `length (nil ++ l2) = length (nil ++ l2)`{.claim}.
    - الحالة 2 (الاستقرائية): سنثبت أن `A -> forall l : list A, S (length (l ++ l2)) = S (length l + length l2)`{.claim}.
      - ليكن `x : A`{.var} و `l : list A`{.var}.
        - العنصر `nat` ينتمي إلى `Type`.
        - العنصر `nat` ينتمي إلى `Type`.
        - العنصر `S` ينتمي إلى `nat -> nat`.
        - العنصر `length (l ++ l2)` ينتمي إلى `nat`.
        - العنصر `length l + length l2` ينتمي إلى `nat`.
        - بشكل خاص `length (l ++ l2) = length l + length l2`{.claim}.
          - حسب فرضية الاستقراء (الاستدعاء التكراري length_app') لدينا `forall (A0 : Type) (l10 l20 : list A0), length (l10 ++ l20) = length l10 + length l20`{.claim}.

        بتطبيق *f_equal*{.just}, لدينا `S (length (l ++ l2)) = S (length l + length l2)`{.claim}.

    هذه الحالات شاملة, نستنتج أن `length (l1 ++ l2) = length l1 + length l2`{.claim}.
