---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: ar
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

ليكن `m : nat`{.var}. سنثبت أن `m + 0 = m`{.claim}.

- لإثبات `m + 0 = m`{.fact} بالاستقراء (nat, nat_ind), نعممها إلى `forall n : nat, n + 0 = n`{.fact}:
- الحالة 1 (الأساس): سنثبت أن `0 + 0 = 0 + 0`{.claim}.
  - حسب تعريف eq (eq_refl), لدينا `0 + 0 = 0 + 0`{.claim} *by Corelib.Init.Logic.eq_refl*.
- الحالة 2 (الاستقرائية): سنثبت أن `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
  - لنأخذ عنصرا اختياريا `m0 : nat`{.var}.
    - لنفرض أن حسب فرضية الاستقراء `m0 + 0 = m0`{.hyp} (IH).
      - حسب IH لدينا `m0 + 0 = m0`{.claim}.
      - باستخدام f_equal نحصل على `forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y`{.claim} *by Corelib.Init.Logic.f_equal*.
      - نستنتج أن `S (m0 + 0) = S m0`{.claim}.
- هذه الحالات شاملة, نستنتج أن `forall n : nat, n + 0 = n`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
- بشكل خاص `m + 0 = m`{.claim}.
