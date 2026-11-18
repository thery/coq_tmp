---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: zh
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# ABCD

✅ 设 `A B C D : Prop`{.var}. 假设 `A -> B -> C -> D`{.hyp} (h1) 且 `A -> C -> B`{.hyp} (h2) 且 `A -> C`{.hyp} (h3) 且 `A`{.hyp} (h4). 我们证明 `D`{.claim}.

- ✅ 根据 h4 我们有 `A`{.claim}.
- ✅ 根据 h4 我们有 `A`{.claim}.
- ✅ 根据 h4 我们有 `A`{.claim}.
- ✅ 根据 h3 我们有 `A -> C`{.claim}.
- ✅ 根据 h2 我们有 `A -> C -> B`{.claim}.
- ✅ 根据 h4 我们有 `A`{.claim}.
- ✅ 根据 h3 我们有 `A -> C`{.claim}.
- ✅ 根据 h1 我们有 `A -> B -> C -> D`{.claim}.
- ✅ 由此可得 `D`{.claim} *by tauto*.
