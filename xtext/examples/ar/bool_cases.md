---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: ar
by: tauto | congruence | lia | firstorder | auto
---

# bool_cases

ليكن `b : bool`{.var}. سنثبت أن `b = true \/ b = false`{.claim}.

- سنثبت أن `b = true \/ b = false` بدراسة الحالات على `b` (bool, match):
  - الحالة 1: سنثبت أن `true = true \/ true = false`{.claim}.
    - حسب تعريف eq (*eq_refl*{.just}), لدينا `true = true`{.claim}.
    - حسب تعريف or (*or_introl*{.just}), لدينا `true = true \/ true = false`{.claim}.
  - الحالة 2: سنثبت أن `false = true \/ false = false`{.claim}.
    - حسب تعريف eq (*eq_refl*{.just}), لدينا `false = false`{.claim}.
    - حسب تعريف or (*or_intror*{.just}), لدينا `false = true \/ false = false`{.claim}.

  هذه الحالات شاملة, نستنتج أن `b = true \/ b = false`{.claim}.
