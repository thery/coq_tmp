---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: zh
by: tauto | congruence | lia | firstorder | auto
---

# drinker

✅ 设 `A : Set`{.var}. 设 `P : A -> Prop`{.var}. 设 `y : A`{.var}. 我们证明 `exists x : A, P x -> forall z : A, P z`{.claim}.

- ✅ 将 *Classical_Prop.classic*{.just}, 我们有 `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.claim} (o).
  - ▫️ 元素 `forall z : A, P z` 属于 `Prop`.
- ✅ 我们证明 `exists x : A, P x -> forall z : A, P z` 分情形讨论，对 *o*{.just} (*or*{.just}, *match*{.just}):
  - ✅ 情形 1: 我们证明 `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
    - ✅ 假设 `forall z : A, P z`{.hyp} (H).
      - ✅ 假设 `P y`{.hyp} (_H). 根据 *H*{.just} 我们有 `forall z : A, P z`{.claim}.
      - ✅ 我们已证明 `P y -> forall z : A, P z`{.claim}.

      根据定义 ex (*ex_intro*{.just}) 取见证 `y`, 我们有 `exists x : A, P x -> forall z : A, P z`{.claim}.
  - ✅ 情形 2: 我们证明 `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
    - ✅ 假设 `~ (forall z : A, P z)`{.hyp} (H).
      - ✅ 将 *Classical_Pred_Type.not_all_ex_not*{.just} 应用于 A, P 且 *H*{.just}, 我们有 `exists n : A, ~ P n`{.claim} (e).
      - ✅ 回到定义 *ex*{.just} (*match*{.just}) 于 *e*{.just}, 我们证明 `exists x : A, P x -> forall z : A, P z`{.claim}:
        - ✅ 任意选取 `t : A`{.var}; 假设 `~ P t`{.hyp} (i).
          - ✅ 假设 `P t`{.hyp} (h).
            - ✅ 由应用, 以 *h*{.just}, 我们有 `False`{.claim} (f).
              - ✅ 根据 *i*{.just} 我们有 `~ P t`, 即 `P t -> False`{.claim}.

            根据矛盾 (*False*{.just}, *match*{.just}), 由 *f*{.just} 可以推出 `forall z : A, P z`{.claim}.
          - ✅ 我们已证明 `P t -> forall z : A, P z`{.claim}.

          根据定义 ex (*ex_intro*{.just}) 取见证 `t`, 我们有 `exists x : A, P x -> forall z : A, P z`{.claim}.

      我们有 `exists x : A, P x -> forall z : A, P z`{.claim}.

  我们有 `exists x : A, P x -> forall z : A, P z`{.claim} 在所有情形下.
