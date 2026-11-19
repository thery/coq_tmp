---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: zh
by: tauto | congruence | lia | firstorder | auto
---

# or_commut

✅ 设 `A B : Prop`{.var}. 假设 `A \/ B`{.hyp} (h). 我们证明 `B \/ A`{.claim}.

- ✅ 我们证明 `B \/ A` 分情形讨论，对 *h*{.just} (*or*{.just}, *match*{.just}):
  - ✅ 情形 1: 我们证明 `A -> B \/ A`{.claim}.
    - ✅ 假设 `A`{.hyp} (i). 根据定义 or (*or_intror*{.just}), 由 *i*{.just} 由此可得 `B \/ A`{.claim}.
  - ✅ 情形 2: 我们证明 `B -> B \/ A`{.claim}.
    - ✅ 假设 `B`{.hyp} (j). 根据定义 or (*or_introl*{.just}), 由 *j*{.just} 由此可得 `B \/ A`{.claim}.

  我们有 `B \/ A`{.claim} 在所有情形下.
