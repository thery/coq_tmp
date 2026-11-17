<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas. -->

# not_not_intro

✅ Let `A : Prop`. Assume `A` (a). We prove `~ ~ A`.

- ▫️ Assume `~ A` (na).
  - ✅ By a we have `A`.
  - ✅ By na we have `~ A`, that is `A -> False`.
  - ✅ We deduce `False`.

