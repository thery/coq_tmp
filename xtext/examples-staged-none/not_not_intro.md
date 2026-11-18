---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
by: tauto | congruence | lia | firstorder | auto
---

# not_not_intro

Let `A : Prop`{.var}. Assume `A`{.hyp} (a). We prove `~ ~ A`{.claim}.

- Assume `~ A`{.hyp} (na).
  - By na we have `~ A`{.claim}, that is `A -> False`{.fact}.
  - By a we have `A`{.claim}.
  - By application, we have `False`{.claim}.
