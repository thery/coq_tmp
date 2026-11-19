---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum_nd

Let `x y z t : Prop`{.var}. Assume `(x -> z) /\ (y -> t)`{.hyp} (H1) and `x /\ y`{.hyp} (H2). We prove `z /\ t`{.claim}.

- By *tauto*{.just} we deduce `z`{.claim}.
  - By *H1*{.just} we have `(x -> z) /\ (y -> t)`{.claim}.
  - By *H2*{.just} we have `x /\ y`{.claim}.
  - Using *proj1*{.just} we get `forall A B : Prop, A /\ B -> A`{.claim}.
  - Using *proj1*{.just} we get `forall A B : Prop, A /\ B -> A`{.claim}.
- By *tauto*{.just} we deduce `t`{.claim}.
  - By *H1*{.just} we have `(x -> z) /\ (y -> t)`{.claim}.
  - By *H2*{.just} we have `x /\ y`{.claim}.
  - Using *proj2*{.just} we get `forall A B : Prop, A /\ B -> B`{.claim}.
  - Using *proj2*{.just} we get `forall A B : Prop, A /\ B -> B`{.claim}.
- So by definition of and (*conj*{.just}), we have `z /\ t`{.claim}.
