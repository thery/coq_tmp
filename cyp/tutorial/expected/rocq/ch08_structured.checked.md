---
by: tauto
---

# praeclarum

✅ Let `x y z t : Prop`{.var}. If `x -> z`{.hyp} and `y -> t`{.hyp} then `x /\ y -> z /\ t`{.claim}.

- ✅ Suppose `x /\ y`{.hyp}.
  - ✅ We get `z`{.claim} by `x -> z`{.fact}, since
    - ✅ we have `x`{.claim}.
  - ✅ We get `t`{.claim} by `y -> t`{.fact}, since
    - ✅ we have `y`{.claim}.

  Altogether we have `z /\ t`{.claim}.
