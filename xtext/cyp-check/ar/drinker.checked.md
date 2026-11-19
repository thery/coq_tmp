---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: ar
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# drinker

✅ ليكن `A : Set`{.var}. ليكن `P : A -> Prop`{.var}. ليكن `y : A`{.var}. سنثبت أن `exists x : A, P x -> forall z : A, P z`{.claim}.

- ✅ بتطبيق *Classical_Prop.classic*{.just}, لدينا `(forall z : A, P z) \/ ~ (forall z : A, P z)`{.claim} (o).
  - ▫️ العنصر `forall z : A, P z` ينتمي إلى `Prop`.
- ✅ سنثبت أن `exists x : A, P x -> forall z : A, P z` بدراسة الحالات على *o*{.just} (*or*{.just}, *match*{.just}):
  - ✅ الحالة 1: سنثبت أن `(forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
    - ✅ لنفرض أن `forall z : A, P z`{.hyp} (H).
      - ✅ لنفرض أن `P y`{.hyp} (_H). حسب *H*{.just} لدينا `forall z : A, P z`{.claim}.
      - ✅ لقد أثبتنا أن `P y -> forall z : A, P z`{.claim}.

      حسب تعريف ex (*ex_intro*{.just}) مع الشاهد `y`, لدينا `exists x : A, P x -> forall z : A, P z`{.claim}.
  - ✅ الحالة 2: سنثبت أن `~ (forall z : A, P z) -> exists x : A, P x -> forall z : A, P z`{.claim}.
    - ✅ لنفرض أن `~ (forall z : A, P z)`{.hyp} (H).
      - ✅ بتطبيق *Classical_Pred_Type.not_all_ex_not*{.just} على A, P و *H*{.just}, لدينا `exists n : A, ~ P n`{.claim} (e).
      - ✅ بالعودة إلى تعريف *ex*{.just} (*match*{.just}) في *e*{.just}, سنثبت أن `exists x : A, P x -> forall z : A, P z`{.claim}:
        - ✅ لنختر اختياريا `t : A`{.var}; لنفرض أن `~ P t`{.hyp} (i).
          - ✅ لنفرض أن `P t`{.hyp} (h).
            - ✅ بالتطبيق, مع *h*{.just}, لدينا `False`{.claim} (f).
              - ✅ حسب *i*{.just} لدينا `~ P t`, أي `P t -> False`{.claim}.

            بالتناقض (*False*{.just}, *match*{.just}), من *f*{.just} يمكننا أن نستنتج أن `forall z : A, P z`{.claim}.
          - ✅ لقد أثبتنا أن `P t -> forall z : A, P z`{.claim}.

          حسب تعريف ex (*ex_intro*{.just}) مع الشاهد `t`, لدينا `exists x : A, P x -> forall z : A, P z`{.claim}.

      لدينا `exists x : A, P x -> forall z : A, P z`{.claim}.

  لدينا `exists x : A, P x -> forall z : A, P z`{.claim} في جميع الحالات.
