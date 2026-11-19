---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
lang: ar
by: tauto | congruence | lia | firstorder | auto
---

# add_0_r'

✅ ليكن `n : nat`{.var}. سنثبت أن `n + 0 = n`{.claim}.

- ✅ سنثبت أن `n + 0 = n` بالاستقراء على `n` (nat, *nat_ind*{.just}):
  - ✅ الحالة 1 (الأساس): سنثبت أن `0 = 0`{.claim}.
    - ✅ حسب تعريف eq (*eq_refl*{.just}), لدينا `0 = 0`{.claim}.
  - ✅ الحالة 2 (الاستقرائية): سنثبت أن `forall m : nat, m + 0 = m -> S m + 0 = S m`{.claim}.
    - ✅ لنختر اختياريا `m : nat`{.var}; لنفرض أن حسب فرضية الاستقراء `m + 0 = m`{.hyp} (IH).
      - ✅ حسب تعريف eq (*eq_refl*{.just}), لدينا `S m = S m`{.claim}.
      - ✅ حسب *IH*{.just} لدينا `m + 0 = m`{.claim}.

      بإعادة الكتابة باستخدام `m + 0 = m`{.fact} من اليمين إلى اليسار (eq_ind_r), نحصل على `S (m + 0) = S m`{.claim}.

  هذه الحالات شاملة, نستنتج أن `n + 0 = n`{.claim}.
