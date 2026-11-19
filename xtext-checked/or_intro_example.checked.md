---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
by: tauto | congruence | lia | firstorder | auto
---

# or_intro_example

✅ Let `A B C : Prop`{.var}. Assume `A`{.hyp} (h). We prove `B \/ A \/ C`{.claim}.

- ✅ By definition of or (or_introl), from `A`{.fact} (h) we deduce `A \/ C`{.claim} *by Corelib.Init.Logic.or_introl*.
- ✅ By definition of or (or_intror), we have `B \/ A \/ C`{.claim} *by Corelib.Init.Logic.or_intror*.
