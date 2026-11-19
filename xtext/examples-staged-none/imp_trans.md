---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
by: tauto | congruence | lia | firstorder | auto
---

# imp_trans

Let `A B C : Prop`{.var}. Assume `A -> B`{.hyp} (f), `B -> C`{.hyp} (g) and `A`{.hyp} (a). We prove `C`{.claim}.

- By *g*{.just} we have `B -> C`{.claim}.
- By application, we have `B`{.claim}.
  - By *f*{.just} we have `A -> B`{.claim}.
  - By *a*{.just} we have `A`{.claim}.
- By application, we have `C`{.claim}.
