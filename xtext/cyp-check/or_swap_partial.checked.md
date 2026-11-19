---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.partial.
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# or_swap_partial (proof in progress)

✅ Let `A B : Prop`{.var}. Assume `A \/ B`{.hyp} (H). We prove `B \/ A`{.claim}.

- ✅ We prove `B \/ A` by case analysis on *H*{.just} (*or*{.just}, *match*{.just}):
  - ✅ Case 1: we prove `A -> B \/ A`{.claim}.
    - 🔶 **[1.1.1]** Assume `A`{.hyp} (a). Prove `B \/ A`{.goal}.

      <details><summary>open goal of the text, not tried: condition 1.1.1, to prove in the Proof block: B \/ A</summary></details>

  - ✅ Case 2: we prove `B -> B \/ A`{.claim}.
    - 🔶 **[1.2.1]** Assume `B`{.hyp} (b). Prove `B \/ A`{.goal}.

      <details><summary>open goal of the text, not tried: condition 1.2.1, to prove in the Proof block: B \/ A</summary></details>


  We have `B \/ A`{.claim} in all cases.
