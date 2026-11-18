---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum_nd

Let `x y z t : Prop`{.var}. Assume `(x -> z) /\ (y -> t)`{.hyp} (H1) and `x /\ y`{.hyp} (H2). We prove `z /\ t`{.claim}.

- By application, we have `z`{.claim}.
  - By application, we have `x -> z`{.claim}.
    - By application, we have `(x -> z) /\ (y -> t) -> x -> z`{.claim}.
      - By application, we have `forall B : Prop, (x -> z) /\ B -> x -> z`{.claim}.
        - By proj1 we have `forall A B : Prop, A /\ B -> A`{.claim}.
        - The element `x -> z`{.fact} belongs to `Prop`{.fact}.
      - The element `y -> t`{.fact} belongs to `Prop`{.fact}.
    - By H1 we have `(x -> z) /\ (y -> t)`{.claim}.
  - By application, we have `x`{.claim}.
    - By application, we have `x /\ y -> x`{.claim}.
      - By application, we have `forall B : Prop, x /\ B -> x`{.claim}.
        - By proj1 we have `forall A B : Prop, A /\ B -> A`{.claim}.
        - The element `x`{.fact} belongs to `Prop`{.fact}.
      - The element `y`{.fact} belongs to `Prop`{.fact}.
    - By H2 we have `x /\ y`{.claim}.
- By application, we have `t`{.claim}.
  - By application, we have `y -> t`{.claim}.
    - By application, we have `(x -> z) /\ (y -> t) -> y -> t`{.claim}.
      - By application, we have `forall B : Prop, (x -> z) /\ B -> B`{.claim}.
        - By proj2 we have `forall A B : Prop, A /\ B -> B`{.claim}.
        - The element `x -> z`{.fact} belongs to `Prop`{.fact}.
      - The element `y -> t`{.fact} belongs to `Prop`{.fact}.
    - By H1 we have `(x -> z) /\ (y -> t)`{.claim}.
  - By application, we have `y`{.claim}.
    - By application, we have `x /\ y -> y`{.claim}.
      - By application, we have `forall B : Prop, x /\ B -> B`{.claim}.
        - By proj2 we have `forall A B : Prop, A /\ B -> B`{.claim}.
        - The element `x`{.fact} belongs to `Prop`{.fact}.
      - The element `y`{.fact} belongs to `Prop`{.fact}.
    - By H2 we have `x /\ y`{.claim}.
- So by definition of and (conj), we have `z /\ t`{.claim} *by Corelib.Init.Logic.conj*.
