---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: it
by: tauto | congruence | lia | firstorder | auto
---

# ABCD

✅ Siano `A B C D : Prop`{.var}. Supponiamo `A -> B -> C -> D`{.hyp} (h1), `A -> C -> B`{.hyp} (h2), `A -> C`{.hyp} (h3) e `A`{.hyp} (h4). Dimostriamo `D`{.claim}.

- ✅ Per *h4*{.just} abbiamo `A`{.claim}.
- ✅ Applicando *h2*{.just}, abbiamo `B`{.claim}.
  - ✅ Per *h4*{.just} abbiamo `A`{.claim}.
  - ✅ Applicando *h3*{.just} a *h4*{.just}, abbiamo `C`{.claim}.
- ✅ Applicando *h3*{.just} a *h4*{.just}, abbiamo `C`{.claim}.
- ✅ Applicando *h1*{.just}, abbiamo `D`{.claim}.
