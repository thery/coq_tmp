---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: ar
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum

✅ لتكن `x y z t : Prop`{.var}. لنفرض أن `(x -> z) /\ (y -> t)`{.hyp} (h1) و `x /\ y`{.hyp} (h2). سنثبت أن `z /\ t`{.claim}.

- ✅ بالعودة إلى تعريف *and*{.just} (*match*{.just}) في *h1*{.just}, سنثبت أن `z /\ t`{.claim}:
  - ✅ لنفرض أن `x -> z`{.hyp} (i) و `y -> t`{.hyp} (j). بالعودة إلى تعريف *and*{.just} (*match*{.just}) في *h2*{.just}, سنثبت أن `z /\ t`{.claim}:
    - ✅ لنفرض أن `x`{.hyp} (k) و `y`{.hyp} (l).
      - ✅ بتطبيق *i*{.just} على *k*{.just}, لدينا `z`{.claim}.
      - ✅ بتطبيق *j*{.just} على *l*{.just}, لدينا `t`{.claim}.

      إذن حسب تعريف and (*conj*{.just}), لدينا `z /\ t`{.claim}.
