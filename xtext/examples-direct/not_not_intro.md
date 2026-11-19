---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
by: tauto | congruence | lia | firstorder | auto
---

# not_not_intro

Let `A : Prop`{.var}. Assume `A`{.hyp} (a). We prove `~ ~ A`{.claim}.

- Assume `~ A`{.hyp} (na).
  - By *a*{.just} we have `A`{.claim}.
  - By *na*{.just} we have `~ A`, that is `A -> False`{.claim}.

  We deduce `False`{.claim}.
