---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: nl
by: tauto | congruence | lia | firstorder | auto
---

# ABCD

✅ Laat `A B C D : Prop`{.var}. Stel `A -> B -> C -> D`{.hyp} (h1), `A -> C -> B`{.hyp} (h2), `A -> C`{.hyp} (h3) en `A`{.hyp} (h4). We bewijzen `D`{.claim}.

- ✅ Volgens h4 er geldt `A`{.claim}.
- ✅ Door toepassing van h2, er geldt `B`{.claim}.
  - ✅ Volgens h4 er geldt `A`{.claim}.
  - ✅ Door toepassing van h3 op h4, er geldt `C`{.claim}.
- ✅ Door toepassing van h3 op h4, er geldt `C`{.claim}.
- ✅ Door toepassing van h1, er geldt `D`{.claim}.
