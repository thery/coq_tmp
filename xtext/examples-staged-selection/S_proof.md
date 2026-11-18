---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
by: tauto | congruence | lia | firstorder | auto
---

# S_proof

Let `A B C : Prop`{.var}. Assume `A -> B -> C`{.hyp} (h), `A -> B`{.hyp} (h0) and `A`{.hyp} (h1). We prove `C`{.claim}.

- Applying h0 to h1, we have `B`{.claim}.
- Applying h to h1, we have `C`{.claim}.
