---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: ar
by: tauto | congruence | lia | firstorder | auto
---

# or_commut

✅ لتكن `A B : Prop`{.var}. لنفرض أن `A \/ B`{.hyp} (h). سنثبت أن `B \/ A`{.claim}.

- ▫️ سنثبت أن `B \/ A`{.fact} بدراسة الحالات على `A \/ B`{.fact} (h) (or, or_ind):
- ✅ الحالة 1: سنثبت أن `A -> B \/ A`{.claim}.
  - ▫️ لنفرض أن `A`{.hyp} (i).
    - ✅ حسب تعريف or (or_intror), من `A`{.fact} (i) نستنتج أن `B \/ A`{.claim} *by Corelib.Init.Logic.or_intror*.
- ✅ الحالة 2: سنثبت أن `B -> B \/ A`{.claim}.
  - ▫️ لنفرض أن `B`{.hyp} (j).
    - ✅ حسب تعريف or (or_introl), من `B`{.fact} (j) نستنتج أن `B \/ A`{.claim} *by Corelib.Init.Logic.or_introl*.
- ✅ لدينا `B \/ A`{.claim} في جميع الحالات.
