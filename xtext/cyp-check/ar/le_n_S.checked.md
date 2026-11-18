---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: ar
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# le_n_S'

✅ لتكن `n m : nat`{.var}. لنفرض أن `n <= m`{.hyp} (H). سنثبت أن `S n <= S m`{.claim}.

- ▫️ سنثبت أن `S n <= S m`{.fact} بالاستقراء على `n <= m`{.fact} (H) (le, le_ind):
- ✅ الحالة 1 (الأساس): سنثبت أن `S n <= S n`{.claim}.
  - ✅ حسب تعريف le (le_n), لدينا `S n <= S n`{.claim} *by Corelib.Init.Peano.le_n*.
- ✅ الحالة 2 (الاستقرائية): سنثبت أن `forall m0 : nat, n <= m0 -> S n <= S m0 -> S n <= S (S m0)`{.claim}.
  - ▫️ لنأخذ عنصرا اختياريا `m0 : nat`{.var}.
    - ▫️ لنفرض أن `n <= m0`{.hyp} (H0) و حسب فرضية الاستقراء `S n <= S m0`{.hyp} (IH).
      - ✅ حسب تعريف le (le_S) مع الشاهد `S m0`{.fact}, من `S n <= S m0`{.fact} (IH) نستنتج أن `S n <= S (S m0)`{.claim} *by Corelib.Init.Peano.le_S*.
- ✅ لدينا `S n <= S m`{.claim} في جميع الحالات.
