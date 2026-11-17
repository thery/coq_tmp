<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis. -->

# praeclarum_nd

✅ Let `x y z t : Prop`. Assume `(x -> z) /\ (y -> t)` (H1) and `x /\ y` (H2). We prove `z /\ t`.

- ✅ We deduce `z`.
  - ✅ By H1 we have `(x -> z) /\ (y -> t)`.
  - ✅ We deduce `x`.
    - ✅ By H2 we have `x /\ y`.
    - ✅ In particular `x /\ y -> x`.
      - ✅ Using proj1 we get `forall A B : Prop, A /\ B -> A` .*by exact @proj1*
  - ✅ In particular `(x -> z) /\ (y -> t) -> x -> z`.
    - ✅ Using proj1 we get `forall A B : Prop, A /\ B -> A` .*by exact @proj1*
- ✅ We deduce `t`.
  - ✅ By H1 we have `(x -> z) /\ (y -> t)`.
  - ✅ We deduce `y`.
    - ✅ By H2 we have `x /\ y`.
    - ✅ In particular `x /\ y -> y`.
      - ✅ Using proj2 we get `forall A B : Prop, A /\ B -> B` .*by exact @proj2*
  - ✅ In particular `(x -> z) /\ (y -> t) -> y -> t`.
    - ✅ Using proj2 we get `forall A B : Prop, A /\ B -> B` .*by exact @proj2*
- ✅ So by definition of and (conj), we have `z /\ t` .*by eapply @conj; eauto*

