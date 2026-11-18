---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: it
by: tauto | congruence | lia | firstorder | auto
---

# S_proof

Siano `A B C : Prop`{.var}. Supponiamo `A -> B -> C`{.hyp} (h), `A -> B`{.hyp} (h0) e `A`{.hyp} (h1). Dimostriamo `C`{.claim}.

- Per h1 abbiamo `A`{.claim}.
- Per h1 abbiamo `A`{.claim}.
- Per h0 abbiamo `A -> B`{.claim}.
- Per h abbiamo `A -> B -> C`{.claim}.
- Ne deduciamo `C`{.claim} *by tauto*.
