---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: ru
by: tauto | congruence | lia | firstorder | auto
---

# ABCD

Пусть `A B C D : Prop`{.var}. Предположим, что `A -> B -> C -> D`{.hyp} (h1) и `A -> C -> B`{.hyp} (h2) и `A -> C`{.hyp} (h3) и `A`{.hyp} (h4). Докажем, что `D`{.claim}.

- По h4 имеем `A`{.claim}.
- По h4 имеем `A`{.claim}.
- По h4 имеем `A`{.claim}.
- По h3 имеем `A -> C`{.claim}.
- По h2 имеем `A -> C -> B`{.claim}.
- По h4 имеем `A`{.claim}.
- По h3 имеем `A -> C`{.claim}.
- По h1 имеем `A -> B -> C -> D`{.claim}.
- Следовательно `D`{.claim} *by tauto*.
