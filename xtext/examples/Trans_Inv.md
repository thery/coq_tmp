---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
by: tauto | congruence | lia | firstorder | auto
---

# Trans_Inv

Let `E : Set`{.var}. Let `R : Rel E`{.var}. Assume `Trans E R`{.hyp} (h). Let `x y z : E`{.var}. Assume `Inv E R x y`{.hyp} (h1) and `Inv E R y z`{.hyp} (h2). We prove `R z x`{.claim}.

- By h2 we have `Inv E R y z`{.claim}.
- By h1 we have `Inv E R x y`{.claim}.
- In particular `R z y -> R y x -> R z x`{.claim}.
  - By h we have `Trans E R`{.claim}.
- We deduce `R z x`{.claim}.
