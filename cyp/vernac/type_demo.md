---
require: From Stdlib Require Import List.
by: auto
---

# type_demo

Let `A : Type`{.var}. Let `l : list A`{.var}. We prove `forall B : Type, forall m : list B, l = l /\ m = m`{.claim}.

- Let `B : Type`{.var}; we prove `forall m : list B, l = l /\ m = m`{.claim}.
  - Let `m : list B`{.var}. We have `l = l /\ m = m`{.claim}.
- Hence `forall B : Type, forall m : list B, l = l /\ m = m`{.claim}.
