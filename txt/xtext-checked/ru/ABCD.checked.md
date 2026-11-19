---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: ru
by: tauto | congruence | lia | firstorder | auto
---

# ABCD

✅ Пусть `A B C D : Prop`{.var}. Предположим, что `A -> B -> C -> D`{.hyp} (h1), `A -> C -> B`{.hyp} (h2), `A -> C`{.hyp} (h3) и `A`{.hyp} (h4). Докажем, что `D`{.claim}.

- ✅ По h4 имеем `A`{.claim}.
- ✅ Применяя h2, имеем `B`{.claim}.
  - ✅ По h4 имеем `A`{.claim}.
  - ✅ Применяя h3 к h4, имеем `C`{.claim}.
- ✅ Применяя h3 к h4, имеем `C`{.claim}.
- ✅ Применяя h1, имеем `D`{.claim}.
