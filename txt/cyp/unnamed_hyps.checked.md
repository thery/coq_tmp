---
by: tauto
---

# unnamed_hyps

✅ Let `A B C : Prop`{.var}. Assume `C`{.hyp}. We prove `A -> B -> A /\ B /\ C`{.claim}.

- ✅ Assume `A`{.hyp}; we prove `B -> A /\ B /\ C`{.claim}.
  - ✅ Assume `B`{.hyp}; we have `A /\ B /\ C`{.claim}.
