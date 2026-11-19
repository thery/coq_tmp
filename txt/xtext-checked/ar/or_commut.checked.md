---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: ar
by: tauto | congruence | lia | firstorder | auto
---

# or_commut

✅ لتكن `A B : Prop`{.var}. لنفرض أن `A \/ B`{.hyp} (h). سنثبت أن `B \/ A`{.claim}.

- ✅ سنثبت أن `B \/ A` بدراسة الحالات على *h*{.just} (*or*{.just}, *match*{.just}):
  - ✅ الحالة 1: سنثبت أن `A -> B \/ A`{.claim}.
    - ✅ لنفرض أن `A`{.hyp} (i). حسب تعريف or (*or_intror*{.just}), من *i*{.just} نستنتج أن `B \/ A`{.claim}.
  - ✅ الحالة 2: سنثبت أن `B -> B \/ A`{.claim}.
    - ✅ لنفرض أن `B`{.hyp} (j). حسب تعريف or (*or_introl*{.just}), من *j*{.just} نستنتج أن `B \/ A`{.claim}.

  لدينا `B \/ A`{.claim} في جميع الحالات.
