---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: ar
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

✅ ليكن `m : nat`{.var}. سنثبت أن `m + 0 = m`{.claim}.

- ▫️ سنثبت أن `m + 0 = m`{.fact} بالاستقراء على `m`{.fact} (nat, nat_ind):
- ✅ الحالة 1 (الأساس): سنثبت أن `0 + 0 = 0 + 0`{.claim}.
  - ✅ حسب تعريف eq (eq_refl), لدينا `0 + 0 = 0 + 0`{.claim} *by Corelib.Init.Logic.eq_refl*.
- ✅ الحالة 2 (الاستقرائية): سنثبت أن `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
  - ▫️ لنختر اختياريا `m0 : nat`{.var}; لنفرض أن حسب فرضية الاستقراء `m0 + 0 = m0`{.hyp} (IH).
    - ▫️ العنصر `nat`{.fact} ينتمي إلى `Type`{.fact}.
    - ▫️ العنصر `nat`{.fact} ينتمي إلى `Type`{.fact}.
    - ▫️ العنصر `S`{.fact} ينتمي إلى `nat -> nat`{.fact}.
    - ▫️ العنصر `m0 + 0`{.fact} ينتمي إلى `nat`{.fact}.
    - ▫️ العنصر `m0`{.fact} ينتمي إلى `nat`{.fact}.
    - ✅ حسب IH لدينا `m0 + 0 = m0`{.claim}.
    - ✅ بتطبيق f_equal, لدينا `S (m0 + 0) = S m0`{.claim}.
- ✅ هذه الحالات شاملة, نستنتج أن `m + 0 = m`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
