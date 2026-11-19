---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: zh
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# S_proof

设 `A B C : Prop`{.var}. 假设 `A -> B -> C`{.hyp} (h), `A -> B`{.hyp} (h0) 且 `A`{.hyp} (h1). 我们证明 `C`{.claim}.

- 根据 h1 我们有 `A`{.claim}.
- 将 h0 应用于 h1, 我们有 `B`{.claim}.
- 将 h, 我们有 `C`{.claim}.
