---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
by: tauto | congruence | lia | firstorder | auto
---

# S_proof

Let `A B C : Prop`{.var}. Assume `A -> B -> C`{.hyp} (h), `A -> B`{.hyp} (h0) and `A`{.hyp} (h1). We prove `C`{.claim}.

- By application, we have `B -> C`{.claim}.
  - By *h*{.just} we have `A -> B -> C`{.claim}.
  - By *h1*{.just} we have `A`{.claim}.
- By application, we have `B`{.claim}.
  - By *h0*{.just} we have `A -> B`{.claim}.
  - By *h1*{.just} we have `A`{.claim}.
- By application, we have `C`{.claim}.
