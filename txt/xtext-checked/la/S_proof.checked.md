---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: la
by: tauto | congruence | lia | firstorder | auto
---

# S_proof

✅ Sint `A B C : Prop`{.var}. Ponamus `A -> B -> C`{.hyp} (h), `A -> B`{.hyp} (h0) et `A`{.hyp} (h1). Ostendamus `C`{.claim}.

- ✅ Per h1 habemus `A`{.claim}.
- ✅ Applicando h0 ad h1, habemus `B`{.claim}.
- ✅ Applicando h, habemus `C`{.claim}.
