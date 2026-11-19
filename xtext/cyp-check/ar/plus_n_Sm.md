---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: ar
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# plus_n_Sm'

لتكن `n m : nat`{.var}. سنثبت أن `S (n + m) = n + S m`{.claim}.

- سنثبت أن `S (n + m) = n + S m` بالاستقراء على `n` (nat, *nat_ind*{.just}):
  - الحالة 1 (الأساس): سنثبت أن `0 + S m = 0 + S m`{.claim}.
    - حسب تعريف eq (*eq_refl*{.just}), لدينا `0 + S m = 0 + S m`{.claim}.
  - الحالة 2 (الاستقرائية): سنثبت أن `forall n0 : nat, S (n0 + m) = n0 + S m -> S (S n0 + m) = S n0 + S m`{.claim}.
    - لنختر اختياريا `n0 : nat`{.var}; لنفرض أن حسب فرضية الاستقراء `S (n0 + m) = n0 + S m`{.hyp} (IH).
      - حسب تعريف eq (*eq_refl*{.just}), لدينا `S (n0 + S m) = S (n0 + S m)`{.claim}.
      - حسب *IH*{.just} لدينا `S (n0 + m) = n0 + S m`{.claim}.

      بإعادة الكتابة باستخدام `S (n0 + m) = n0 + S m`{.fact} من اليمين إلى اليسار (eq_ind_r), نحصل على `S (S (n0 + m)) = S (n0 + S m)`{.claim}.

  هذه الحالات شاملة, نستنتج أن `S (n + m) = n + S m`{.claim}.
