---
by: tauto | auto
---

# structure

✅ Let `P Q R : Prop`{.var}. Assume `P -> Q`{.hyp} (pq) and `Q -> R`{.hyp} (qr). We prove `P -> R /\ Q`{.claim}.

- ✅ Assume `P`{.hyp} (p).  Then:
  - ✅ By *pq*{.just} and *p*{.just}, we have `Q`{.claim} (q).
  - ✅ By *qr*{.just} and *q*{.just}, we have `R`{.claim} (r).

  So, with *r*{.just} and *q*{.just}, we have `R /\ Q`{.claim}.
- ✅ Hence `P -> R /\ Q`{.claim}.
