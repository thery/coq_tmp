<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis. -->

# praeclarum_nd

✅ Let `x y z t : Prop`. Assume `(x -> z) /\ (y -> t)` (H1) and `x /\ y` (H2). We prove `z /\ t`.

- ✅ We deduce `z` .*by tauto*
  - ✅ By H1 we have `(x -> z) /\ (y -> t)`.
  - ✅ By H2 we have `x /\ y`.
  - ✅ Using proj1 we get `forall A B : Prop, A /\ B -> A` .*by exact @Corelib.Init.Logic.proj1*
  - ✅ Using proj1 we get `forall A B : Prop, A /\ B -> A` .*by exact @Corelib.Init.Logic.proj1*
- ✅ We deduce `t` .*by tauto*
  - ✅ By H1 we have `(x -> z) /\ (y -> t)`.
  - ✅ By H2 we have `x /\ y`.
  - ✅ Using proj2 we get `forall A B : Prop, A /\ B -> B` .*by exact @Corelib.Init.Logic.proj2*
  - ✅ Using proj2 we get `forall A B : Prop, A /\ B -> B` .*by exact @Corelib.Init.Logic.proj2*
- ✅ So by definition of and (conj), we have `z /\ t` .*by eapply @conj; eauto*

