---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: de
by: tauto | congruence | lia | firstorder | auto
---

# S_proof

Seien `A B C : Prop`{.var}. Angenommen `A -> B -> C`{.hyp} (h) und `A -> B`{.hyp} (h0) und `A`{.hyp} (h1). Wir zeigen `C`{.claim}.

- Nach h1 es gilt `A`{.claim}.
- Nach h1 es gilt `A`{.claim}.
- Nach h0 es gilt `A -> B`{.claim}.
- Nach h es gilt `A -> B -> C`{.claim}.
- Daraus folgt `C`{.claim} *by tauto*.
