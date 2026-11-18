---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# rev_app_distr

✅ Let `A : Type`{.var}. Let `x y : list A`{.var}. We prove `rev (x ++ y) = rev y ++ rev x`{.claim}.

- ▫️ To prove `rev (x ++ y) = rev y ++ rev x`{.fact} by induction (list, list_ind), we generalise it to `forall l : list A, rev (l ++ y) = rev y ++ rev l`{.fact}:
- ✅ Case 1 (base): we prove `rev (nil ++ y) = rev y ++ rev nil`{.claim}.
  - ✅ By definition of eq (eq_refl), we have `rev y = rev y`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - ❌ Applying app_nil_r, we have `rev y ++ nil = rev y`{.claim}.

    <details><summary>not proved: rev y ++ [] = rev y</summary></details>

    - ▫️ The element `A`{.fact} belongs to `Type`{.fact}.
    - ▫️ The element `rev y`{.fact} belongs to `list A`{.fact}.
  - ✅ Rewriting with `rev y ++ nil = rev y`{.fact} from right to left (eq_ind_r), we get `rev y = rev y ++ nil`{.claim}.
- ✅ Case 2 (inductive): we prove `forall (a : A) (l : list A), rev (l ++ y) = rev y ++ rev l -> rev ((a :: l) ++ y) = rev y ++ rev (a :: l)`{.claim}.
  - ▫️ Let `a : A`{.var} and `l : list A`{.var}; assume by induction hypothesis `rev (l ++ y) = rev y ++ rev l`{.hyp} (IHl).
    - ✅ Rewriting with `rev y ++ rev l ++ a :: nil = (rev y ++ rev l) ++ a :: nil`{.fact} from right to left (eq_ind_r), we get `(rev y ++ rev l) ++ a :: nil = rev y ++ rev l ++ a :: nil`{.claim}.
      - ✅ By definition of eq (eq_refl), we have `(rev y ++ rev l) ++ a :: nil = (rev y ++ rev l) ++ a :: nil`{.claim} *by Corelib.Init.Logic.eq_refl*.
      - ❌ Applying app_assoc, we have `rev y ++ rev l ++ a :: nil = (rev y ++ rev l) ++ a :: nil`{.claim}.

        <details><summary>not proved: rev y ++ rev l ++ [a] = (rev y ++ rev l) ++ [a]</summary></details>

        - ▫️ The element `A`{.fact} belongs to `Type`{.fact}.
        - ▫️ The element `rev y`{.fact} belongs to `list A`{.fact}.
        - ▫️ The element `rev l`{.fact} belongs to `list A`{.fact}.
        - ▫️ The element `a :: nil`{.fact} belongs to `list A`{.fact}.
    - ✅ By IHl we have `rev (l ++ y) = rev y ++ rev l`{.claim}.
    - ✅ Rewriting with `rev (l ++ y) = rev y ++ rev l`{.fact} from right to left (eq_ind_r), we get `rev (l ++ y) ++ a :: nil = rev y ++ rev l ++ a :: nil`{.claim}.
- ✅ These cases being exhaustive, we deduce `forall l : list A, rev (l ++ y) = rev y ++ rev l`{.claim} *by Corelib.Init.Datatypes.list_ind*.
- ✅ In particular `rev (x ++ y) = rev y ++ rev x`{.claim}.
