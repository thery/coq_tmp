---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: ar
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# ABCD

✅ لتكن `A B C D : Prop`{.var}. لنفرض أن `A -> B -> C -> D`{.hyp} (h1), `A -> C -> B`{.hyp} (h2), `A -> C`{.hyp} (h3) و `A`{.hyp} (h4). سنثبت أن `D`{.claim}.

- ✅ حسب h4 لدينا `A`{.claim}.
- ✅ بتطبيق h2, لدينا `B`{.claim}.
  - ✅ حسب h4 لدينا `A`{.claim}.
  - ✅ بتطبيق h3 على h4, لدينا `C`{.claim}.
- ✅ بتطبيق h3 على h4, لدينا `C`{.claim}.
- ✅ بتطبيق h1, لدينا `D`{.claim}.
