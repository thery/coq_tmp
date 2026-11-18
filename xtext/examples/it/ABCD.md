---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: it
by: tauto | congruence | lia | firstorder | auto
---

# ABCD

Siano `A B C D : Prop`{.var}. Supponiamo `A -> B -> C -> D`{.hyp} (h1) e `A -> C -> B`{.hyp} (h2) e `A -> C`{.hyp} (h3) e `A`{.hyp} (h4). Dimostriamo `D`{.claim}.

- Per h4 abbiamo `A`{.claim}.
- Per h4 abbiamo `A`{.claim}.
- Per h4 abbiamo `A`{.claim}.
- Per h3 abbiamo `A -> C`{.claim}.
- Per h2 abbiamo `A -> C -> B`{.claim}.
- Per h4 abbiamo `A`{.claim}.
- Per h3 abbiamo `A -> C`{.claim}.
- Per h1 abbiamo `A -> B -> C -> D`{.claim}.
- Ne deduciamo `D`{.claim} *by tauto*.
