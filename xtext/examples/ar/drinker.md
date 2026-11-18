---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: ar
by: tauto | congruence | lia | firstorder | auto
---

# drinker

ليكن `A : Set`{.var}. ليكن `P : A -> Prop`{.var}. ليكن `y : A`{.var}. سنثبت أن `exists x : A, P x -> forall z : A, P z`{.claim}.

- بشكل خاص `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.claim} (o).
  - باستخدام classic نحصل على `forall P0 : Prop, P0 \/ ~ P0`{.claim} *by Stdlib.Logic.Classical_Prop.classic*.
- سنثبت أن `exists x : A, P x -> forall z : A, P z`{.fact} بدراسة الحالات على `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.fact} (o) (or, match):
- الحالة 1: سنثبت أن `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - لنفرض أن `forall z : A, P z`{.hyp} (H).
    - لنفرض أن `P y`{.hyp} (_H).
      - حسب H لدينا `forall z : A, P z`{.claim}.
    - لقد أثبتنا أن `P y -> forall z : A, P z`{.claim}.
    - حسب تعريف ex (ex_intro) مع الشاهد `y`{.fact}, لدينا `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- الحالة 2: سنثبت أن `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
  - لنفرض أن `~ (forall z : A, P z)`{.hyp} (H).
    - نستنتج أن `exists n : A, ~ P n`{.claim} (e).
      - حسب H لدينا `~ (forall z : A, P z)`{.claim}.
      - باستخدام not_all_ex_not نحصل على `forall (U : Type) (P0 : U -> Prop), ~ (forall n : U, P0 n) -> exists n : U, ~ P0 n`{.claim} *by Stdlib.Logic.Classical_Pred_Type.not_all_ex_not*.
    - بالعودة إلى تعريف ex (match) في `exists n : A, ~ P n`{.fact} (e), سنثبت أن `exists x : A, P x -> forall z : A, P z`{.claim}:
      - لنأخذ عنصرا اختياريا `t : A`{.var}.
        - لنفرض أن `~ P t`{.hyp} (i).
          - لنفرض أن `P t`{.hyp} (h).
            - نستنتج أن `False`{.claim} (f).
              - حسب h لدينا `P t`{.claim}.
              - حسب i لدينا `~ P t`{.claim}, أي `P t -> False`{.fact}.
            - بالتناقض (False, match), من `False`{.fact} (f) يمكننا أن نستنتج أن `forall z : A, P z`{.claim}.
          - لقد أثبتنا أن `P t -> forall z : A, P z`{.claim}.
          - حسب تعريف ex (ex_intro) مع الشاهد `t`{.fact}, لدينا `exists x : A, P x -> forall z : A, P z`{.claim} *by Corelib.Init.Logic.ex_intro*.
- لدينا `exists x : A, P x -> forall z : A, P z`{.claim} في جميع الحالات.
