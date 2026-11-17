<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis. -->

# ABCD

✅ Let `A B C D : Prop`. Assume `A -> B -> C -> D` (h1) and `A -> C -> B` (h2) and `A -> C` (h3) and `A` (h4). We prove `D`.

- ✅ By h4 we have `A`.
- ✅ We deduce `B`.
  - ✅ By h4 we have `A`.
  - ✅ We deduce `C`.
    - ✅ By h4 we have `A`.
    - ✅ By h3 we have `A -> C`.
  - ✅ By h2 we have `A -> C -> B`.
- ✅ We deduce `C`.
  - ✅ By h4 we have `A`.
  - ✅ By h3 we have `A -> C`.
- ✅ By h1 we have `A -> B -> C -> D`.
- ✅ We deduce `D`.

