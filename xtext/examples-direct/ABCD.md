---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
by: tauto | congruence | lia | firstorder | auto
---

# ABCD

Let `A B C D : Prop`{.var}. Assume `A -> B -> C -> D`{.hyp} (h1), `A -> C -> B`{.hyp} (h2), `A -> C`{.hyp} (h3) and `A`{.hyp} (h4). We prove `D`{.claim}.

- By *h4*{.just} we have `A`{.claim}.
- By *h4*{.just} we have `A`{.claim}.
- By *h4*{.just} we have `A`{.claim}.
- By *h3*{.just} we have `A -> C`{.claim}.
- By *h2*{.just} we have `A -> C -> B`{.claim}.
- By *h4*{.just} we have `A`{.claim}.
- By *h3*{.just} we have `A -> C`{.claim}.
- By *h1*{.just} we have `A -> B -> C -> D`{.claim}.
- By *tauto*{.just} we deduce `D`{.claim}.
