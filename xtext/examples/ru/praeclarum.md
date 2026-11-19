---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: ru
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum

Пусть `x y z t : Prop`{.var}. Предположим, что `(x -> z) /\ (y -> t)`{.hyp} (h1) и `x /\ y`{.hyp} (h2). Докажем, что `z /\ t`{.claim}.

- Возвращаясь к определению and (*and_ind*{.just}) в *h1*{.just}, докажем, что `z /\ t`{.claim}:
  - Предположим, что `x -> z`{.hyp} (i) и `y -> t`{.hyp} (j). Возвращаясь к определению and (*and_ind*{.just}) в *h2*{.just}, докажем, что `z /\ t`{.claim}:
    - Предположим, что `x`{.hyp} (k) и `y`{.hyp} (l).
      - Применяя *i*{.just} к *k*{.just}, имеем `z`{.claim}.
      - Применяя *j*{.just} к *l*{.just}, имеем `t`{.claim}.

      Тогда по определению and (*conj*{.just}), имеем `z /\ t`{.claim}.
