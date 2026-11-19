---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: zh
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# ABCD

✅ 设 `A B C D : Prop`{.var}. 假设 `A -> B -> C -> D`{.hyp} (h1), `A -> C -> B`{.hyp} (h2), `A -> C`{.hyp} (h3) 且 `A`{.hyp} (h4). 我们证明 `D`{.claim}.

- ✅ 根据 *h4*{.just} 我们有 `A`{.claim}.
- ✅ 将 *h2*{.just}, 我们有 `B`{.claim}.
  - ✅ 根据 *h4*{.just} 我们有 `A`{.claim}.
  - ✅ 将 *h3*{.just} 应用于 *h4*{.just}, 我们有 `C`{.claim}.
- ✅ 将 *h3*{.just} 应用于 *h4*{.just}, 我们有 `C`{.claim}.
- ✅ 将 *h1*{.just}, 我们有 `D`{.claim}.
