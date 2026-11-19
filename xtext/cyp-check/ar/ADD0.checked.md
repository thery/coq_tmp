---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: ar
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

✅ ليكن `m : nat`{.var}. سنثبت أن `m + 0 = m`{.claim}.

- ✅ سنثبت أن `m + 0 = m` بالاستقراء على *m*{.just} (*nat*{.just}, *induction*{.just}):
  - ✅ الحالة 1 (الأساس): سنثبت أن `0 + 0 = 0 + 0`{.claim}.
    - ✅ حسب تعريف eq (*eq_refl*{.just}), لدينا `0 + 0 = 0 + 0`{.claim}.
  - ✅ الحالة 2 (الاستقرائية): سنثبت أن `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
    - ✅ لنختر اختياريا `m0 : nat`{.var}; لنفرض أن حسب فرضية الاستقراء `m0 + 0 = m0`{.hyp} (IH).
      - ▫️ العنصر `nat` ينتمي إلى `Type`.
      - ▫️ العنصر `nat` ينتمي إلى `Type`.
      - ▫️ العنصر `S` ينتمي إلى `nat -> nat`.
      - ▫️ العنصر `m0 + 0` ينتمي إلى `nat`.
      - ✅ حسب *IH*{.just} لدينا `m0 + 0 = m0`{.claim}.

      بتطبيق *f_equal*{.just}, لدينا `S (m0 + 0) = S m0`{.claim}.

  هذه الحالات شاملة, نستنتج أن `m + 0 = m`{.claim}.
