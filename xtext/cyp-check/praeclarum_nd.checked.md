---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum_nd

✅ Let `x y z t : Prop`{.var}. Assume `(x -> z) /\ (y -> t)`{.hyp} (H1) and `x /\ y`{.hyp} (H2). We prove `z /\ t`{.claim}.

- ✅ We deduce `z`{.claim} *by tauto*.
  - ✅ By H1 we have `(x -> z) /\ (y -> t)`{.claim}.
  - ✅ By H2 we have `x /\ y`{.claim}.
  - ✅ Using proj1 we get `forall A B : Prop, A /\ B -> A`{.claim} *by Corelib.Init.Logic.proj1*.
  - ✅ Using proj1 we get `forall A B : Prop, A /\ B -> A`{.claim} *by Corelib.Init.Logic.proj1*.
- ✅ We deduce `t`{.claim} *by tauto*.
  - ✅ By H1 we have `(x -> z) /\ (y -> t)`{.claim}.
  - ✅ By H2 we have `x /\ y`{.claim}.
  - ✅ Using proj2 we get `forall A B : Prop, A /\ B -> B`{.claim} *by Corelib.Init.Logic.proj2*.
  - ✅ Using proj2 we get `forall A B : Prop, A /\ B -> B`{.claim} *by Corelib.Init.Logic.proj2*.
- ✅ So by definition of and (conj), we have `z /\ t`{.claim} *by Corelib.Init.Logic.conj*.
