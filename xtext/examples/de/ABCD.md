---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: de
by: tauto | congruence | lia | firstorder | auto
---

# ABCD

Seien `A B C D : Prop`{.var}. Angenommen `A -> B -> C -> D`{.hyp} (h1), `A -> C -> B`{.hyp} (h2), `A -> C`{.hyp} (h3) und `A`{.hyp} (h4). Wir zeigen `D`{.claim}.

- Nach h4 es gilt `A`{.claim}.
- Nach h4 es gilt `A`{.claim}.
- Nach h4 es gilt `A`{.claim}.
- Nach h3 es gilt `A -> C`{.claim}.
- Nach h2 es gilt `A -> C -> B`{.claim}.
- Nach h4 es gilt `A`{.claim}.
- Nach h3 es gilt `A -> C`{.claim}.
- Nach h1 es gilt `A -> B -> C -> D`{.claim}.
- Daraus folgt `D`{.claim} *by tauto*.
