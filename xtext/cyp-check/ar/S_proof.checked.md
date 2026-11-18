---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: ar
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# S_proof

✅ لتكن `A B C : Prop`{.var}. لنفرض أن `A -> B -> C`{.hyp} (h) و `A -> B`{.hyp} (h0) و `A`{.hyp} (h1). سنثبت أن `C`{.claim}.

- ✅ حسب h1 لدينا `A`{.claim}.
- ✅ حسب h1 لدينا `A`{.claim}.
- ✅ حسب h0 لدينا `A -> B`{.claim}.
- ✅ حسب h لدينا `A -> B -> C`{.claim}.
- ✅ نستنتج أن `C`{.claim} *by tauto*.
