---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: ar
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# S_proof

لتكن `A B C : Prop`{.var}. لنفرض أن `A -> B -> C`{.hyp} (h), `A -> B`{.hyp} (h0) و `A`{.hyp} (h1). سنثبت أن `C`{.claim}.

- حسب *h1*{.just} لدينا `A`{.claim}.
- بتطبيق *h0*{.just} على *h1*{.just}, لدينا `B`{.claim}.
- بتطبيق *h*{.just}, لدينا `C`{.claim}.
