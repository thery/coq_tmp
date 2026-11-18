---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# rev_app_distr

Let `A : Type`{.var}. Let `x y : list A`{.var}. We prove `rev (x ++ y) = rev y ++ rev x`{.claim}.

- To prove `rev (x ++ y) = rev y ++ rev x`{.fact} by induction (list, list_ind), we generalise it to `forall l : list A, rev (l ++ y) = rev y ++ rev l`{.fact}:
- Case 1 (base): we prove `rev (nil ++ y) = rev y ++ rev nil`{.claim}.
  - By definition of eq (eq_refl), we have `rev y = rev y`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - In particular `rev y ++ nil = rev y`{.claim}.
    - Using app_nil_r we get `forall (A0 : Type) (l : list A0), l ++ nil = l`{.claim} *by Stdlib.Lists.List.app_nil_r*.
  - Rewriting with `rev y ++ nil = rev y`{.fact} from right to left (eq_ind_r), we get `rev y = rev y ++ nil`{.claim}.
- Case 2 (inductive): we prove `forall (a : A) (l : list A), rev (l ++ y) = rev y ++ rev l -> rev ((a :: l) ++ y) = rev y ++ rev (a :: l)`{.claim}.
  - Let `a : A`{.var}.
  - Let `l : list A`{.var}.
  - Assume by induction hypothesis `rev (l ++ y) = rev y ++ rev l`{.hyp} (IHl).
    - Rewriting with `rev y ++ rev l ++ a :: nil = (rev y ++ rev l) ++ a :: nil`{.fact} from right to left (eq_ind_r), we get `(rev y ++ rev l) ++ a :: nil = rev y ++ rev l ++ a :: nil`{.claim}.
      - By definition of eq (eq_refl), we have `(rev y ++ rev l) ++ a :: nil = (rev y ++ rev l) ++ a :: nil`{.claim} *by Corelib.Init.Logic.eq_refl*.
      - In particular `rev y ++ rev l ++ a :: nil = (rev y ++ rev l) ++ a :: nil`{.claim}.
        - Using app_assoc we get `forall (A0 : Type) (l0 m n : list A0), l0 ++ m ++ n = (l0 ++ m) ++ n`{.claim} *by Stdlib.Lists.List.app_assoc*.
    - By IHl we have `rev (l ++ y) = rev y ++ rev l`{.claim}.
    - Rewriting with `rev (l ++ y) = rev y ++ rev l`{.fact} from right to left (eq_ind_r), we get `rev (l ++ y) ++ a :: nil = rev y ++ rev l ++ a :: nil`{.claim}.
- These cases being exhaustive, we deduce `forall l : list A, rev (l ++ y) = rev y ++ rev l`{.claim} *by Corelib.Init.Datatypes.list_ind*.
- In particular `rev (x ++ y) = rev y ++ rev x`{.claim}.
