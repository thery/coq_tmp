---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
by: tauto | congruence | lia | firstorder | auto
---

# imp_trans

Let `A B C : Prop`{.var}. Assume `A -> B`{.hyp} (f) and `B -> C`{.hyp} (g) and `A`{.hyp} (a). We prove `C`{.claim}.

- We deduce `B`{.claim}.
  - By a we have `A`{.claim}.
  - By f we have `A -> B`{.claim}.
- By g we have `B -> C`{.claim}.
- We deduce `C`{.claim}.
