---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
by: tauto | congruence | lia | firstorder | auto
---

# double_neg_em

Let `A : Prop`{.var}. We prove `~ ~ (A \/ ~ A)`{.claim}.

- Assume `~ (A \/ ~ A)`{.hyp} (H).
  - By definition of or (or_intror), we have `A \/ ~ A`{.claim} *by Corelib.Init.Logic.or_intror*.
    - Assume `A`{.hyp} (a).
      - By definition of or (or_introl), from `A`{.fact} (a) we deduce `A \/ ~ A`{.claim} *by Corelib.Init.Logic.or_introl*.
      - Applying H, we have `False`{.claim}.
    - We have proved `A -> False`{.claim}.
  - Applying H, we have `False`{.claim}.
