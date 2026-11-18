---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum_nd

✅ Let `x y z t : Prop`{.var}. Assume `(x -> z) /\ (y -> t)`{.hyp} (H1) and `x /\ y`{.hyp} (H2). We prove `z /\ t`{.claim}.

- ✅ Applying proj1, we have `z`{.claim}.
  - ▫️ The element `x -> z`{.fact} belongs to `Prop`{.fact}.
  - ▫️ The element `y -> t`{.fact} belongs to `Prop`{.fact}.
  - ✅ By H1 we have `(x -> z) /\ (y -> t)`{.claim}.
  - ✅ Applying proj1 to x, y and H2, we have `x`{.claim}.
- ✅ Applying proj2, we have `t`{.claim}.
  - ▫️ The element `x -> z`{.fact} belongs to `Prop`{.fact}.
  - ▫️ The element `y -> t`{.fact} belongs to `Prop`{.fact}.
  - ✅ By H1 we have `(x -> z) /\ (y -> t)`{.claim}.
  - ✅ Applying proj2 to x, y and H2, we have `y`{.claim}.
- ✅ So by definition of and (conj), we have `z /\ t`{.claim} *by Corelib.Init.Logic.conj*.
