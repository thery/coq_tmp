---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: zh
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# bool_cases

✅ 设 `b : bool`{.var}. 我们证明 `b = true \/ b = false`{.claim}.

- ✅ 我们证明 `b = true \/ b = false` 分情形讨论，对 *b*{.just} (*bool*{.just}, *match*{.just}):
  - ✅ 情形 1: 我们证明 `true = true \/ true = false`{.claim}.
    - ✅ 根据定义 eq (*eq_refl*{.just}), 我们有 `true = true`{.claim}.
    - ✅ 根据定义 or (*or_introl*{.just}), 我们有 `true = true \/ true = false`{.claim}.
  - ✅ 情形 2: 我们证明 `false = true \/ false = false`{.claim}.
    - ✅ 根据定义 eq (*eq_refl*{.just}), 我们有 `false = false`{.claim}.
    - ✅ 根据定义 or (*or_intror*{.just}), 我们有 `false = true \/ false = false`{.claim}.

  这些情形是穷尽的, 由此可得 `b = true \/ b = false`{.claim}.
