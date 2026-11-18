---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
by: tauto | congruence | lia | firstorder | auto
---

# double_neg_em

Let `A : Prop`{.var}. We prove `~ ~ (A \/ ~ A)`{.claim}.

- Assume `~ (A \/ ~ A)`{.hyp} (H).
  - By H we have `~ (A \/ ~ A)`{.claim}, that is `A \/ ~ A -> False`{.fact} (P1).
  - By definition of or (or_intror), we have `A \/ ~ A`{.claim} *by Corelib.Init.Logic.or_intror*.
    - Assume `A`{.hyp} (a).
      - By H we have `~ (A \/ ~ A)`{.claim}, that is `A \/ ~ A -> False`{.fact} (P2.1).
      - By definition of or (or_introl), from `A`{.fact} (a) we deduce `A \/ ~ A`{.claim} *by Corelib.Init.Logic.or_introl*.
      - Applying P2.1, we have `False`{.claim}.
    - We have proved `A -> False`{.claim}.
  - Applying P1, we have `False`{.claim}.
