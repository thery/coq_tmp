---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: it
by: tauto | congruence | lia | firstorder | auto
---

# S_proof

✅ Siano `A B C : Prop`{.var}. Supponiamo `A -> B -> C`{.hyp} (h), `A -> B`{.hyp} (h0) e `A`{.hyp} (h1). Dimostriamo `C`{.claim}.

- ✅ Per h1 abbiamo `A`{.claim}.
- ✅ Applicando h0 a h1, abbiamo `B`{.claim}.
- ✅ Applicando h, abbiamo `C`{.claim}.
