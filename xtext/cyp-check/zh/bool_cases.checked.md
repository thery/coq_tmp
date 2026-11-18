---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: zh
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# bool_cases

✅ 设 `b : bool`{.var}. 我们证明 `b = true \/ b = false`{.claim}.

- ▫️ 我们证明 `b = true \/ b = false`{.fact} 分情形讨论，对 `b`{.fact} (bool, match):
- ✅ 情形 1: 我们证明 `true = true \/ true = false`{.claim}.
  - ✅ 根据定义 eq (eq_refl), 我们有 `true = true`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - ✅ 根据定义 or (or_introl), 我们有 `true = true \/ true = false`{.claim} *by Corelib.Init.Logic.or_introl*.
- ✅ 情形 2: 我们证明 `false = true \/ false = false`{.claim}.
  - ✅ 根据定义 eq (eq_refl), 我们有 `false = false`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - ✅ 根据定义 or (or_intror), 我们有 `false = true \/ false = false`{.claim} *by Corelib.Init.Logic.or_intror*.
- ❌ 这些情形是穷尽的, 由此可得 `b = true \/ b = false`{.claim}.

  <details><summary>not proved: b = true \/ b = false</summary></details>

