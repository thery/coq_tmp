---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# rev_involutive

Let `A : Type`{.var}. Let `l : list A`{.var}. We prove `rev (rev l) = l`{.claim}.

- To prove `rev (rev l) = l`{.fact} by induction (list, list_ind), we generalise it to `forall l0 : list A, rev (rev l0) = l0`{.fact}:
- Case 1 (base): we prove `(nil) = (nil) :> list A`{.claim}.
  - By definition of eq (eq_refl), we have `(nil) = (nil) :> list A`{.claim} *by eapply @eq_refl; eauto*.
- Case 2 (inductive): we prove `forall (a : A) (l0 : list A), rev (rev l0) = l0 -> rev (rev (a :: l0)) = a :: l0`{.claim}.
  - Let `a : A`{.var}.
  - Let `l0 : list A`{.var}.
  - Assume by induction hypothesis `rev (rev l0) = l0`{.hyp} (IHl).
    - Rewriting with `rev (rev l0) = l0`{.fact} from right to left (eq_ind_r), we get `a :: rev (rev l0) = a :: l0`{.claim}.
      - By definition of eq (eq_refl), we have `a :: l0 = a :: l0`{.claim} *by eapply @eq_refl; eauto*.
      - By IHl we have `rev (rev l0) = l0`{.claim}.
    - In particular `rev (rev l0 ++ a :: nil) = a :: rev (rev l0)`{.claim}.
      - Using rev_unit we get `forall (A0 : Type) (l1 : list A0) (a0 : A0), rev (l1 ++ a0 :: nil) = a0 :: rev l1`{.claim} *by exact @rev_unit*.
    - Rewriting with `rev (rev l0 ++ a :: nil) = a :: rev (rev l0)`{.fact} from right to left (eq_ind_r), we get `rev (rev l0 ++ a :: nil) = a :: l0`{.claim}.
- These cases being exhaustive, we deduce `forall l0 : list A, rev (rev l0) = l0`{.claim} *by eapply (@list_ind (A) (fun l0 : list A => rev (rev l0) = l0)); cbv beta; eauto*.
- In particular `rev (rev l) = l`{.claim}.
