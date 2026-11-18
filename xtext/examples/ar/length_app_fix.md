---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: ar
by: tauto | congruence | lia | firstorder | auto
---

# length_app'

سنثبت أن `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim}.

- سنثبت أن `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim} بالتكرار على `l1`{.fact} (fix length_app'):
  - ليكن `A : Type`{.var}.
  - لتكن `l1 l2 : list A`{.var}.
  - سنثبت أن `length (l1 ++ l2) = length l1 + length l2`{.fact} بالاستقراء على `l1`{.fact} (list, match):
  - الحالة 1 (الأساس): سنثبت أن `length (nil ++ l2) = length (nil ++ l2)`{.claim}.
    - حسب تعريف eq (eq_refl), لدينا `length (nil ++ l2) = length (nil ++ l2)`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - الحالة 2 (الاستقرائية): سنثبت أن `A -> forall l : list A, S (length (l ++ l2)) = S (length l + length l2)`{.claim}.
    - ليكن `x : A`{.var}.
    - ليكن `l : list A`{.var}.
    - حسب فرضية الاستقراء (الاستدعاء التكراري length_app') لدينا `forall (A0 : Type) (l10 l20 : list A0), length (l10 ++ l20) = length l10 + length l20`{.claim}.
    - باستخدام f_equal نحصل على `forall (A0 B : Type) (f : A0 -> B) (x0 y : A0), x0 = y -> f x0 = f y`{.claim} *by Corelib.Init.Logic.f_equal*.
    - نستنتج أن `S (length (l ++ l2)) = S (length l + length l2)`{.claim} *by congruence*.
  - هذه الحالات شاملة, نستنتج أن `length (l1 ++ l2) = length l1 + length l2`{.claim}.
