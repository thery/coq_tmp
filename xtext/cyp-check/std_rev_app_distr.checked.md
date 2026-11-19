---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# rev_app_distr

✅ Let `A : Type`{.var}. Let `x y : list A`{.var}. We prove `rev (x ++ y) = rev y ++ rev x`{.claim}.

- ✅ We prove `rev (x ++ y) = rev y ++ rev x` by induction on `x` (list, *list_ind*{.just}):
  - ✅ Case 1 (base): we prove `rev (nil ++ y) = rev y ++ rev nil`{.claim}.
    - ✅ By definition of eq (*eq_refl*{.just}), we have `rev y = rev y`{.claim}.
    - ✅ Applying *List.app_nil_r*{.just}, we have `rev y ++ nil = rev y`{.claim}.
      - ▫️ The element `rev y` belongs to `list A`.
    - ✅ Rewriting with `rev y ++ nil = rev y`{.fact} from right to left (eq_ind_r), we get `rev y = rev y ++ nil`{.claim}.
  - ✅ Case 2 (inductive): we prove `forall (a : A) (l : list A), rev (l ++ y) = rev y ++ rev l -> rev ((a :: l) ++ y) = rev y ++ rev (a :: l)`{.claim}.
    - ✅ Let `a : A`{.var} and `l : list A`{.var}; assume by induction hypothesis `rev (l ++ y) = rev y ++ rev l`{.hyp} (IHl).
      - ✅ Rewriting with `rev y ++ rev l ++ a :: nil = (rev y ++ rev l) ++ a :: nil`{.fact} from right to left (eq_ind_r), we get `(rev y ++ rev l) ++ a :: nil = rev y ++ rev l ++ a :: nil`{.claim}.
        - ✅ By definition of eq (*eq_refl*{.just}), we have `(rev y ++ rev l) ++ a :: nil = (rev y ++ rev l) ++ a :: nil`{.claim}.
        - ✅ Applying *List.app_assoc*{.just}, we have `rev y ++ rev l ++ a :: nil = (rev y ++ rev l) ++ a :: nil`{.claim}.
          - ▫️ The element `rev y` belongs to `list A`.
          - ▫️ The element `rev l` belongs to `list A`.
          - ▫️ The element `a :: nil` belongs to `list A`.
      - ✅ By *IHl*{.just} we have `rev (l ++ y) = rev y ++ rev l`{.claim}.

      Rewriting with `rev (l ++ y) = rev y ++ rev l`{.fact} from right to left (eq_ind_r), we get `rev (l ++ y) ++ a :: nil = rev y ++ rev l ++ a :: nil`{.claim}.

  These cases being exhaustive, we deduce `rev (x ++ y) = rev y ++ rev x`{.claim}.
