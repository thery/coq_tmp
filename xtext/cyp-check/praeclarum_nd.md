---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum_nd

Let `x y z t : Prop`{.var}. Assume `(x -> z) /\ (y -> t)`{.hyp} (H1) and `x /\ y`{.hyp} (H2). We prove `z /\ t`{.claim}.

- We deduce `z`{.claim}.
  - By H1 we have `(x -> z) /\ (y -> t)`{.claim}.
  - We deduce `x`{.claim}.
    - By H2 we have `x /\ y`{.claim}.
    - In particular `x /\ y -> x`{.claim}.
      - Using proj1 we get `forall A B : Prop, A /\ B -> A`{.claim} *by exact @proj1*.
  - In particular `(x -> z) /\ (y -> t) -> x -> z`{.claim}.
    - Using proj1 we get `forall A B : Prop, A /\ B -> A`{.claim} *by exact @proj1*.
- We deduce `t`{.claim}.
  - By H1 we have `(x -> z) /\ (y -> t)`{.claim}.
  - We deduce `y`{.claim}.
    - By H2 we have `x /\ y`{.claim}.
    - In particular `x /\ y -> y`{.claim}.
      - Using proj2 we get `forall A B : Prop, A /\ B -> B`{.claim} *by exact @proj2*.
  - In particular `(x -> z) /\ (y -> t) -> y -> t`{.claim}.
    - Using proj2 we get `forall A B : Prop, A /\ B -> B`{.claim} *by exact @proj2*.
- So by definition of and (conj), we have `z /\ t`{.claim} *by eapply @conj; eauto*.
