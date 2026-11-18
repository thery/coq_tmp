---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# rev_involutive

Let `A : Type`{.var}. Let `l : list A`{.var}. We prove `rev (rev l) = l`{.claim}.

- To prove `rev (rev l) = l`{.fact} by induction (list, list_ind), we generalise it to `forall l0 : list A, rev (rev l0) = l0`{.fact}:
- Case 1 (base): we prove `nil = (@nil A)`{.claim}.
  - By definition of eq (eq_refl), we have `nil = (@nil A)`{.claim} *by Corelib.Init.Logic.eq_refl*.
- Case 2 (inductive): we prove `forall (a : A) (l0 : list A), rev (rev l0) = l0 -> rev (rev (a :: l0)) = a :: l0`{.claim}.
  - Let `a : A`{.var}.
    - Let `l0 : list A`{.var}.
      - Assume `rev (rev l0) = l0`{.hyp} (IHl).
        - Rewriting with `rev (rev l0) = l0`{.fact} from right to left (eq_ind_r), we get `a :: rev (rev l0) = a :: l0`{.claim}.
          - By definition of eq (eq_refl), we have `a :: l0 = a :: l0`{.claim} *by Corelib.Init.Logic.eq_refl*.
          - By IHl we have `rev (rev l0) = l0`{.claim}.
        - By application, we have `rev (rev l0 ++ a :: nil) = a :: rev (rev l0)`{.claim}.
          - By application, we have `forall elpi_ctx_entry_5_ : A, rev (rev l0 ++ elpi_ctx_entry_5_ :: nil) = elpi_ctx_entry_5_ :: rev (rev l0)`{.claim}.
            - By application, we have `forall (elpi_ctx_entry_5_ : list A) (elpi_ctx_entry_6_ : A), rev (elpi_ctx_entry_5_ ++ elpi_ctx_entry_6_ :: nil) = elpi_ctx_entry_6_ :: rev elpi_ctx_entry_5_`{.claim}.
              - By rev_unit we have `forall (elpi_ctx_entry_5_ : Type) (elpi_ctx_entry_6_ : list elpi_ctx_entry_5_) (elpi_ctx_entry_7_ : elpi_ctx_entry_5_), rev (elpi_ctx_entry_6_ ++ elpi_ctx_entry_7_ :: nil) = elpi_ctx_entry_7_ :: rev elpi_ctx_entry_6_`{.claim}.
              - The element `A`{.fact} belongs to `Type`{.fact}.
            - The element `rev l0`{.fact} belongs to `list A`{.fact}.
          - The element `a`{.fact} belongs to `A`{.fact}.
        - Rewriting with `rev (rev l0 ++ a :: nil) = a :: rev (rev l0)`{.fact} from right to left (eq_ind_r), we get `rev (rev l0 ++ a :: nil) = a :: l0`{.claim}.
- These cases being exhaustive, we deduce `forall l0 : list A, rev (rev l0) = l0`{.claim} *by Corelib.Init.Datatypes.list_ind*.
- In particular `rev (rev l) = l`{.claim}.
