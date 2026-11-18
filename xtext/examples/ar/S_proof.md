---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: ar
by: tauto | congruence | lia | firstorder | auto
---

# S_proof

لتكن `A B C : Prop`{.var}. لنفرض أن `A -> B -> C`{.hyp} (h), `A -> B`{.hyp} (h0) و `A`{.hyp} (h1). سنثبت أن `C`{.claim}.

- حسب h1 لدينا `A`{.claim}.
- بتطبيق h0 على h1, لدينا `B`{.claim}.
- بتطبيق h, لدينا `C`{.claim}.
