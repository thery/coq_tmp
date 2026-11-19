---
by: tauto | auto
---

# scope_demo

Let `P Q : Prop`{.var}. If `P -> Q`{.hyp} (f) then `forall x : nat, P -> Q /\ x = x`{.claim}.

- Let `x : nat`{.var}; we prove `P -> Q /\ x = x`{.claim}.
  - Assume `P`{.hyp} (p).
    - By *f*{.just} we have `Q`{.claim}.
    - And we have `x = x`{.claim}.

    So `Q /\ x = x`{.claim}.
- Hence `forall x : nat, P -> Q /\ x = x`{.claim}.
