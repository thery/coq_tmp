---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# rev_app_distr

Let `A : Type`{.var}. Let `x y : list A`{.var}. We prove `rev (x ++ y) = rev y ++ rev x`{.claim}.

- To prove `rev (x ++ y) = rev y ++ rev x`{.fact} by induction (list, list_ind), we generalise it to `forall l : list A, rev (l ++ y) = rev y ++ rev l`{.fact}:
- Case 1 (base): we prove `rev (nil ++ y) = rev y ++ rev nil`{.claim}.
  - By definition of eq (eq_refl), we have `rev y = rev y`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - By application, we have `rev y ++ nil = rev y`{.claim}.
    - By application, we have `forall l : list A, l ++ nil = l`{.claim}.
      - By app_nil_r we have `forall (A0 : Type) (l : list A0), l ++ nil = l`{.claim}.
      - The element `A`{.fact} belongs to `Type`{.fact}.
    - The element `rev y`{.fact} belongs to `list A`{.fact}.
  - Rewriting with `rev y ++ nil = rev y`{.fact} from right to left (eq_ind_r), we get `rev y = rev y ++ nil`{.claim}.
- Case 2 (inductive): we prove `forall (a : A) (l : list A), rev (l ++ y) = rev y ++ rev l -> rev ((a :: l) ++ y) = rev y ++ rev (a :: l)`{.claim}.
  - Let `a : A`{.var}.
    - Let `l : list A`{.var}.
      - Assume `rev (l ++ y) = rev y ++ rev l`{.hyp} (IHl).
        - Rewriting with `rev y ++ rev l ++ a :: nil = (rev y ++ rev l) ++ a :: nil`{.fact} from right to left (eq_ind_r), we get `(rev y ++ rev l) ++ a :: nil = rev y ++ rev l ++ a :: nil`{.claim}.
          - By definition of eq (eq_refl), we have `(rev y ++ rev l) ++ a :: nil = (rev y ++ rev l) ++ a :: nil`{.claim} *by Corelib.Init.Logic.eq_refl*.
          - By application, we have `rev y ++ rev l ++ a :: nil = (rev y ++ rev l) ++ a :: nil`{.claim}.
            - By application, we have `forall n : list A, rev y ++ rev l ++ n = (rev y ++ rev l) ++ n`{.claim}.
              - By application, we have `forall m n : list A, rev y ++ m ++ n = (rev y ++ m) ++ n`{.claim}.
                - By application, we have `forall l0 m n : list A, l0 ++ m ++ n = (l0 ++ m) ++ n`{.claim}.
                  - By app_assoc we have `forall (A0 : Type) (l0 m n : list A0), l0 ++ m ++ n = (l0 ++ m) ++ n`{.claim}.
                  - The element `A`{.fact} belongs to `Type`{.fact}.
                - The element `rev y`{.fact} belongs to `list A`{.fact}.
              - The element `rev l`{.fact} belongs to `list A`{.fact}.
            - The element `a :: nil`{.fact} belongs to `list A`{.fact}.
        - By IHl we have `rev (l ++ y) = rev y ++ rev l`{.claim}.
        - Rewriting with `rev (l ++ y) = rev y ++ rev l`{.fact} from right to left (eq_ind_r), we get `rev (l ++ y) ++ a :: nil = rev y ++ rev l ++ a :: nil`{.claim}.
- These cases being exhaustive, we deduce `forall l : list A, rev (l ++ y) = rev y ++ rev l`{.claim} *by Corelib.Init.Datatypes.list_ind*.
- In particular `rev (x ++ y) = rev y ++ rev x`{.claim}.
