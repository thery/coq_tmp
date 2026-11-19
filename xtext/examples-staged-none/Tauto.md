---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
by: tauto | congruence | lia | firstorder | auto
---

# Tauto

Let `A B C : Prop`{.var}. Assume `A`{.hyp} (h1), `B`{.hyp} (h2) and `A -> B -> C`{.hyp} (h3). We prove `C`{.claim}.

- By application, we have `B -> C`{.claim}.
  - By *h3*{.just} we have `A -> B -> C`{.claim}.
  - By *h1*{.just} we have `A`{.claim}.
- By *h2*{.just} we have `B`{.claim}.
- By application, we have `C`{.claim}.
