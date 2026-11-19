---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: ar
by: tauto | congruence | lia | firstorder | auto
---

# le_n_S'

لتكن `n m : nat`{.var}. لنفرض أن `n <= m`{.hyp} (H). سنثبت أن `S n <= S m`{.claim}.

- سنثبت أن `S n <= S m` بالاستقراء على *H*{.just} (*le*{.just}, *induction*{.just}):
  - الحالة 1 (الأساس): سنثبت أن `S n <= S n`{.claim}.
    - حسب تعريف le (*le_n*{.just}), لدينا `S n <= S n`{.claim}.
  - الحالة 2 (الاستقرائية): سنثبت أن `forall m0 : nat, n <= m0 -> S n <= S m0 -> S n <= S (S m0)`{.claim}.
    - لنختر اختياريا `m0 : nat`{.var}; لنفرض أن `n <= m0`{.hyp} (H0) و حسب فرضية الاستقراء `S n <= S m0`{.hyp} (IH). حسب تعريف le (*le_S*{.just}) مع الشاهد `S m0`, من *IH*{.just} نستنتج أن `S n <= S (S m0)`{.claim}.

  لدينا `S n <= S m`{.claim} في جميع الحالات.
