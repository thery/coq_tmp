<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis. -->

# Tauto

✅ Let `A B C : Prop`. Assume `A` (h1) and `B` (h2) and `A -> B -> C` (h3). We prove `C`.

- ✅ By h1 we have `A`.
- ✅ By h2 we have `B`.
- ✅ By h3 we have `A -> B -> C`.
- ✅ We deduce `C`.

