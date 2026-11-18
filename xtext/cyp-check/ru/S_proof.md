---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: ru
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# S_proof

Пусть `A B C : Prop`{.var}. Предположим, что `A -> B -> C`{.hyp} (h) и `A -> B`{.hyp} (h0) и `A`{.hyp} (h1). Докажем, что `C`{.claim}.

- По h1 имеем `A`{.claim}.
- По h1 имеем `A`{.claim}.
- По h0 имеем `A -> B`{.claim}.
- По h имеем `A -> B -> C`{.claim}.
- Следовательно `C`{.claim} *by tauto*.
