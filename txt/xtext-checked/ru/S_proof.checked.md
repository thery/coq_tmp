---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: ru
by: tauto | congruence | lia | firstorder | auto
---

# S_proof

✅ Пусть `A B C : Prop`{.var}. Предположим, что `A -> B -> C`{.hyp} (h), `A -> B`{.hyp} (h0) и `A`{.hyp} (h1). Докажем, что `C`{.claim}.

- ✅ По *h1*{.just} имеем `A`{.claim}.
- ✅ Применяя *h0*{.just} к *h1*{.just}, имеем `B`{.claim}.
- ✅ Применяя *h*{.just}, имеем `C`{.claim}.
