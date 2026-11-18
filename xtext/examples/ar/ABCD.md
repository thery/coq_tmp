---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: ar
by: tauto | congruence | lia | firstorder | auto
---

# ABCD

لتكن `A B C D : Prop`{.var}. لنفرض أن `A -> B -> C -> D`{.hyp} (h1), `A -> C -> B`{.hyp} (h2), `A -> C`{.hyp} (h3) و `A`{.hyp} (h4). سنثبت أن `D`{.claim}.

- حسب h4 لدينا `A`{.claim}.
- حسب h4 لدينا `A`{.claim}.
- حسب h4 لدينا `A`{.claim}.
- حسب h3 لدينا `A -> C`{.claim}.
- حسب h2 لدينا `A -> C -> B`{.claim}.
- حسب h4 لدينا `A`{.claim}.
- حسب h3 لدينا `A -> C`{.claim}.
- حسب h1 لدينا `A -> B -> C -> D`{.claim}.
- نستنتج أن `D`{.claim} *by tauto*.
