---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
by: tauto | congruence | lia | firstorder | auto
---

# imp_trans

Let `A B C : Prop`{.var}. Assume `A -> B`{.hyp} (f), `B -> C`{.hyp} (g) and `A`{.hyp} (a). We prove `C`{.claim}.

- Applying *f*{.just} to *a*{.just}, we have `B`{.claim} (P1).
- Applying *g*{.just} to *P1*{.just}, we have `C`{.claim}.
