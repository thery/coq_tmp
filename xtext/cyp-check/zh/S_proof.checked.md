---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: zh
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# S_proof

✅ 设 `A B C : Prop`{.var}. 假设 `A -> B -> C`{.hyp} (h) 且 `A -> B`{.hyp} (h0) 且 `A`{.hyp} (h1). 我们证明 `C`{.claim}.

- ✅ 根据 h1 我们有 `A`{.claim}.
- ✅ 根据 h1 我们有 `A`{.claim}.
- ✅ 根据 h0 我们有 `A -> B`{.claim}.
- ✅ 根据 h 我们有 `A -> B -> C`{.claim}.
- ✅ 由此可得 `C`{.claim} *by tauto*.
