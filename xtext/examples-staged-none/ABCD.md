---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
by: tauto | congruence | lia | firstorder | auto
---

# ABCD

Let `A B C D : Prop`{.var}. Assume `A -> B -> C -> D`{.hyp} (h1), `A -> C -> B`{.hyp} (h2), `A -> C`{.hyp} (h3) and `A`{.hyp} (h4). We prove `D`{.claim}.

- By application, we have `C -> D`{.claim}.
  - By application, we have `B -> C -> D`{.claim}.
    - By h1 we have `A -> B -> C -> D`{.claim}.
    - By h4 we have `A`{.claim}.
  - By application, we have `B`{.claim}.
    - By application, we have `C -> B`{.claim}.
      - By h2 we have `A -> C -> B`{.claim}.
      - By h4 we have `A`{.claim}.
    - By application, we have `C`{.claim}.
      - By h3 we have `A -> C`{.claim}.
      - By h4 we have `A`{.claim}.
- By application, we have `C`{.claim}.
  - By h3 we have `A -> C`{.claim}.
  - By h4 we have `A`{.claim}.
- By application, we have `D`{.claim}.
