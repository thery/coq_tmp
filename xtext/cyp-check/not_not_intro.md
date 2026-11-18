---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# not_not_intro

Let `A : Prop`{.var}. Assume `A`{.hyp} (a). We prove `~ ~ A`{.claim}.

- Assume `~ A`{.hyp} (na).
  - By na we have `~ A`{.claim}, that is `A -> False`{.fact}.
  - By application, with a, we have `False`{.claim}.
