---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
by: tauto | congruence | lia | firstorder | auto
---

# double_neg_em

Let `A : Prop`{.var}. We prove `~ ~ (A \/ ~ A)`{.claim}.

- Assume `~ (A \/ ~ A)`{.hyp} (H).
  - By definition of or (or_intror), we have `A \/ ~ A`{.claim} *by eapply @or_intror; eauto*.
    - Assume `A`{.hyp} (a).
      - By definition of or (or_introl), from `A`{.fact} (a) we deduce `A \/ ~ A`{.claim} *by eapply @or_introl; eauto*.
      - By H we have `~ (A \/ ~ A)`{.claim}.
      - We deduce `False`{.claim}.
    - We have proved `A -> False`{.claim}.
  - By H we have `~ (A \/ ~ A)`{.claim}.
  - We deduce `False`{.claim}.
