---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
by: tauto | congruence | lia | firstorder | auto
---

# ABCD

Let `A B C D : Prop`{.var}. Assume `A -> B -> C -> D`{.hyp} (h1), `A -> C -> B`{.hyp} (h2), `A -> C`{.hyp} (h3) and `A`{.hyp} (h4). We prove `D`{.claim}.

- Applying *h2*{.just} to *h4*{.just}, we have `B`{.claim}.
  - Applying *h3*{.just} to *h4*{.just}, we have `C`{.claim}.
- Applying *h3*{.just} to *h4*{.just}, we have `C`{.claim}.
- Applying *h1*{.just} to *h4*{.just}, we have `D`{.claim}.
