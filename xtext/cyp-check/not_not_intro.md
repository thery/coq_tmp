---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# not_not_intro

Let `A : Prop`{.var}. Assume `A`{.hyp} (a). We prove `~ ~ A`{.claim}.

- Assume `~ A`{.hyp} (na).
  - By *na*{.just} we have `~ A`, that is `A -> False`{.claim}.

  By application, with *a*{.just}, we have `False`{.claim}.
