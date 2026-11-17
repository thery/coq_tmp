---
by: tauto | auto
---

# scope_demo

Let `P Q : Prop`. If `P -> Q` (f) then `forall x : nat, P -> Q /\ x = x`.

- Let `x : nat`.
  - Assume `P` (p).
    - By f we have `Q`.
    - And we have `x = x`.
- Hence `forall x : nat, P -> Q /\ x = x`.
