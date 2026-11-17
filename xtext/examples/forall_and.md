---
require: From Stdlib Require Import Arith Lia List. Import ListNotations. Require Import XText.lemmas.
by: tauto | congruence | lia | firstorder | auto
---

# forall_and

Let `P Q : nat -> Prop`{.var}. Assume `forall x : nat, P x /\ Q x`{.hyp} (H). Let `x : nat`{.var}. We prove `P x`{.claim}.

- In particular `P x /\ Q x`{.claim}.
  - By H we have `forall x0 : nat, P x0 /\ Q x0`{.claim}.
- We have proved `P x /\ Q x -> P x`{.claim}.
  - Assume `P x /\ Q x`{.hyp} (a).
    - Going back to the definition of and (match) in `P x /\ Q x`{.fact} (a), we prove `P x`{.claim}:
      - Assume `P x`{.hyp} (p) and `Q x`{.hyp} (_H).
        - By p we have `P x`{.claim}.
- We deduce `P x`{.claim}.
