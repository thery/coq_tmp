---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: zh
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# or_commut

设 `A B : Prop`{.var}. 假设 `A \/ B`{.hyp} (h). 我们证明 `B \/ A`{.claim}.

- 我们证明 `B \/ A`{.fact} 分情形讨论，对 `A \/ B`{.fact} (h) (or, or_ind):
- 情形 1: 我们证明 `A -> B \/ A`{.claim}.
  - 假设 `A`{.hyp} (i).
    - 根据定义 or (or_intror), 由 `A`{.fact} (i) 由此可得 `B \/ A`{.claim} *by Corelib.Init.Logic.or_intror*.
- 情形 2: 我们证明 `B -> B \/ A`{.claim}.
  - 假设 `B`{.hyp} (j).
    - 根据定义 or (or_introl), 由 `B`{.fact} (j) 由此可得 `B \/ A`{.claim} *by Corelib.Init.Logic.or_introl*.
- 我们有 `B \/ A`{.claim} 在所有情形下.
