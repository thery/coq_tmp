---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: ru
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum

Пусть `x y z t : Prop`{.var}. Предположим, что `(x -> z) /\ (y -> t)`{.hyp} (h1) и `x /\ y`{.hyp} (h2). Докажем, что `z /\ t`{.claim}.

- Возвращаясь к определению and (and_ind) в `(x -> z) /\ (y -> t)`{.fact} (h1), докажем, что `z /\ t`{.claim}:
  - Предположим, что `x -> z`{.hyp} (i) и `y -> t`{.hyp} (j).
    - Возвращаясь к определению and (and_ind) в `x /\ y`{.fact} (h2), докажем, что `z /\ t`{.claim}:
      - Предположим, что `x`{.hyp} (k) и `y`{.hyp} (l).
        - Следовательно `z`{.claim}.
          - По k имеем `x`{.claim}.
          - По i имеем `x -> z`{.claim}.
        - Следовательно `t`{.claim}.
          - По l имеем `y`{.claim}.
          - По j имеем `y -> t`{.claim}.
        - Тогда по определению and (conj), имеем `z /\ t`{.claim} *by Corelib.Init.Logic.conj*.
