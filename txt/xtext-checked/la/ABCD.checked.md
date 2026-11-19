---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: la
by: tauto | congruence | lia | firstorder | auto
---

# ABCD

✅ Sint `A B C D : Prop`{.var}. Ponamus `A -> B -> C -> D`{.hyp} (h1), `A -> C -> B`{.hyp} (h2), `A -> C`{.hyp} (h3) et `A`{.hyp} (h4). Ostendamus `D`{.claim}.

- ✅ Per *h4*{.just} habemus `A`{.claim}.
- ✅ Applicando *h2*{.just}, habemus `B`{.claim}.
  - ✅ Per *h4*{.just} habemus `A`{.claim}.
  - ✅ Applicando *h3*{.just} ad *h4*{.just}, habemus `C`{.claim}.
- ✅ Applicando *h3*{.just} ad *h4*{.just}, habemus `C`{.claim}.
- ✅ Applicando *h1*{.just}, habemus `D`{.claim}.
