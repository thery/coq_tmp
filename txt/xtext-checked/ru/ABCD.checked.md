---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: ru
by: tauto | congruence | lia | firstorder | auto
---

# ABCD

✅ Пусть `A B C D : Prop`{.var}. Предположим, что `A -> B -> C -> D`{.hyp} (h1), `A -> C -> B`{.hyp} (h2), `A -> C`{.hyp} (h3) и `A`{.hyp} (h4). Докажем, что `D`{.claim}.

- ✅ По *h4*{.just} имеем `A`{.claim}.
- ✅ Применяя *h2*{.just}, имеем `B`{.claim}.
  - ✅ По *h4*{.just} имеем `A`{.claim}.
  - ✅ Применяя *h3*{.just} к *h4*{.just}, имеем `C`{.claim}.
- ✅ Применяя *h3*{.just} к *h4*{.just}, имеем `C`{.claim}.
- ✅ Применяя *h1*{.just}, имеем `D`{.claim}.
