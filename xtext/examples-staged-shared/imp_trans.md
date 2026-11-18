---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
by: tauto | congruence | lia | firstorder | auto
---

# imp_trans

Let `A B C : Prop`{.var}. Assume `A -> B`{.hyp} (f), `B -> C`{.hyp} (g) and `A`{.hyp} (a). We prove `C`{.claim}.

- Applying f to a, we have `B`{.claim} (P1).
- Applying g to P1, we have `C`{.claim}.
