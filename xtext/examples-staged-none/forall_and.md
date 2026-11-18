---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
by: tauto | congruence | lia | firstorder | auto
---

# forall_and

Let `P Q : nat -> Prop`{.var}. Assume `forall x : nat, P x /\ Q x`{.hyp} (H). Let `x : nat`{.var}. We prove `P x`{.claim}.

- By application, we have `P x /\ Q x`{.claim} (a).
  - By H we have `forall elpi_ctx_entry_4_ : nat, P elpi_ctx_entry_4_ /\ Q elpi_ctx_entry_4_`{.claim}.
  - The element `x`{.fact} belongs to `nat`{.fact}.
- Going back to the definition of and (match) in `P x /\ Q x`{.fact} (a), we prove `P x`{.claim}:
  - Assume `P x`{.hyp} (p).
    - Assume `Q x`{.hyp} (_H).
      - By p we have `P x`{.claim}.
