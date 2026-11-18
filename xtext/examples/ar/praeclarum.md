---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: ar
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum

لتكن `x y z t : Prop`{.var}. لنفرض أن `(x -> z) /\ (y -> t)`{.hyp} (h1) و `x /\ y`{.hyp} (h2). سنثبت أن `z /\ t`{.claim}.

- بالعودة إلى تعريف and (and_ind) في `(x -> z) /\ (y -> t)`{.fact} (h1), سنثبت أن `z /\ t`{.claim}:
  - لنفرض أن `x -> z`{.hyp} (i) و `y -> t`{.hyp} (j).
    - بالعودة إلى تعريف and (and_ind) في `x /\ y`{.fact} (h2), سنثبت أن `z /\ t`{.claim}:
      - لنفرض أن `x`{.hyp} (k) و `y`{.hyp} (l).
        - نستنتج أن `z`{.claim}.
          - حسب k لدينا `x`{.claim}.
          - حسب i لدينا `x -> z`{.claim}.
        - نستنتج أن `t`{.claim}.
          - حسب l لدينا `y`{.claim}.
          - حسب j لدينا `y -> t`{.claim}.
        - إذن حسب تعريف and (conj), لدينا `z /\ t`{.claim} *by Corelib.Init.Logic.conj*.
