---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
by: tauto | congruence | lia | firstorder | auto
---

# ABCD

Let `A B C D : Prop`{.var}. Assume `A -> B -> C -> D`{.hyp} (h1) and `A -> C -> B`{.hyp} (h2) and `A -> C`{.hyp} (h3) and `A`{.hyp} (h4). We prove `D`{.claim}.

- By h4 we have `A`{.claim}.
- We deduce `B`{.claim}.
  - By h4 we have `A`{.claim}.
  - We deduce `C`{.claim}.
    - By h4 we have `A`{.claim}.
    - By h3 we have `A -> C`{.claim}.
  - By h2 we have `A -> C -> B`{.claim}.
- We deduce `C`{.claim}.
  - By h4 we have `A`{.claim}.
  - By h3 we have `A -> C`{.claim}.
- By h1 we have `A -> B -> C -> D`{.claim}.
- We deduce `D`{.claim}.
