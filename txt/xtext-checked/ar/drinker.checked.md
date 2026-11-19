---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: ar
by: tauto | congruence | lia | firstorder | auto
---

# drinker

✅ ليكن `A : Set`{.var}. ليكن `P : A -> Prop`{.var}. ليكن `y : A`{.var}. سنثبت أن `exists x : A, P x -> forall z : A, P z`{.claim}.

- ✅ بتطبيق classic, لدينا `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.claim} (o).
  - ▫️ العنصر `forall z : A, P z`{.fact} ينتمي إلى `Prop`{.fact}.
- ▫️ سنثبت أن `exists x : A, P x -> forall z : A, P z`{.fact} بدراسة الحالات على `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.fact} (o) (or, match):
- ✅ الحالة 1: سنثبت أن `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - ▫️ لنفرض أن `forall z : A, P z`{.hyp} (H).
    - ▫️ لنفرض أن `P y`{.hyp} (_H).
      - ✅ حسب H لدينا `forall z : A, P z`{.claim}.
    - ✅ لقد أثبتنا أن `P y -> forall z : A, P z`{.claim}.
    - ✅ حسب تعريف ex (ex_intro) مع الشاهد `y`{.fact}, لدينا `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- ✅ الحالة 2: سنثبت أن `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - ▫️ لنفرض أن `~ (forall z : A, P z)`{.hyp} (H).
    - ❌ بتطبيق not_all_ex_not على A, P و H, لدينا `exists n : A, ~ P n`{.claim} (e).

      <details><summary>not proved: exists n : A, ~ P n</summary></details>

    - ✅ بالعودة إلى تعريف ex (match) في `exists n : A, ~ P n`{.fact} (e), سنثبت أن `exists x : A, P x -> forall z : A, P z`{.claim}:
      - ▫️ لنختر اختياريا `t : A`{.var}; لنفرض أن `~ P t`{.hyp} (i).
        - ▫️ لنفرض أن `P t`{.hyp} (h).
          - ✅ بالتطبيق, مع h, لدينا `False`{.claim} (f).
            - ✅ حسب i لدينا `~ P t`{.claim}, أي `P t -> False`{.fact}.
          - ✅ بالتناقض (False, match), من `False`{.fact} (f) يمكننا أن نستنتج أن `forall z : A, P z`{.claim}.
        - ✅ لقد أثبتنا أن `P t -> forall z : A, P z`{.claim}.
        - ✅ حسب تعريف ex (ex_intro) مع الشاهد `t`{.fact}, لدينا `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- ✅ لدينا `exists x : A, P x -> forall z : A, P z`{.claim} في جميع الحالات.
