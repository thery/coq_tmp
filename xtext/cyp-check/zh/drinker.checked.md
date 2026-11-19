---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: zh
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# drinker

✅ 设 `A : Set`{.var}. 设 `P : A -> Prop`{.var}. 设 `y : A`{.var}. 我们证明 `exists x : A, P x -> forall z : A, P z`{.claim}.

- ✅ 将 classic, 我们有 `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.claim} (o).
  - ▫️ 元素 `forall z : A, P z`{.fact} 属于 `Prop`{.fact}.
- ▫️ 我们证明 `exists x : A, P x -> forall z : A, P z`{.fact} 分情形讨论，对 `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.fact} (o) (or, match):
- ✅ 情形 1: 我们证明 `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - ▫️ 假设 `forall z : A, P z`{.hyp} (H).
    - ▫️ 假设 `P y`{.hyp} (_H).
      - ✅ 根据 H 我们有 `forall z : A, P z`{.claim}.
    - ✅ 我们已证明 `P y -> forall z : A, P z`{.claim}.
    - ✅ 根据定义 ex (ex_intro) 取见证 `y`{.fact}, 我们有 `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- ✅ 情形 2: 我们证明 `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - ▫️ 假设 `~ (forall z : A, P z)`{.hyp} (H).
    - ❌ 将 not_all_ex_not 应用于 A, P 且 H, 我们有 `exists n : A, ~ P n`{.claim} (e).

      <details><summary>not proved: exists n : A, ~ P n</summary></details>

    - ✅ 回到定义 ex (match) 于 `exists n : A, ~ P n`{.fact} (e), 我们证明 `exists x : A, P x -> forall z : A, P z`{.claim}:
      - ▫️ 任意选取 `t : A`{.var}; 假设 `~ P t`{.hyp} (i).
        - ▫️ 假设 `P t`{.hyp} (h).
          - ✅ 由应用, 以 h, 我们有 `False`{.claim} (f).
            - ✅ 根据 i 我们有 `~ P t`{.claim}, 即 `P t -> False`{.fact}.
          - ✅ 根据矛盾 (False, match), 由 `False`{.fact} (f) 可以推出 `forall z : A, P z`{.claim}.
        - ✅ 我们已证明 `P t -> forall z : A, P z`{.claim}.
        - ✅ 根据定义 ex (ex_intro) 取见证 `t`{.fact}, 我们有 `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- ✅ 我们有 `exists x : A, P x -> forall z : A, P z`{.claim} 在所有情形下.
