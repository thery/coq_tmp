---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
by: tauto | congruence | lia | firstorder | auto
---

# ABCD

Let `A B C D : Prop`{.var}. Assume `A -> B -> C -> D`{.hyp} (h1), `A -> C -> B`{.hyp} (h2), `A -> C`{.hyp} (h3) and `A`{.hyp} (h4). We prove `D`{.claim}.

- By h4 we have `A`{.claim}.
- Applying h2, we have `B`{.claim}.
  - By h4 we have `A`{.claim}.
  - Applying h3 to h4, we have `C`{.claim}.
- Applying h3 to h4, we have `C`{.claim}.
- Applying h1, we have `D`{.claim}.
