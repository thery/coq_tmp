---
require: From Stdlib Require Import List.
by: auto
---

# type_demo

Let `A : Type`. Let `l : list A`. We prove `forall B : Type, forall m : list B, l = l /\ m = m`.

- Let `B : Type`.
  - Let `m : list B`.
    - We have `l = l` and `m = m`.
- Hence `forall B : Type, forall m : list B, l = l /\ m = m`.
