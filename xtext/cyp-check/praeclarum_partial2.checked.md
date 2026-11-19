---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.partial.
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum_partial2 (proof in progress)

✅ Let `x y z t : Prop`{.var}. Assume `(x -> z) /\ (y -> t)`{.hyp} (H). We prove `x /\ y -> z /\ t`{.claim}.

- ✅ Going back to the definition of *and*{.just} (*match*{.just}) in *H*{.just}, we prove `x /\ y -> z /\ t`{.claim}:
  - ✅ Assume `x -> z`{.hyp} (Hxz), `y -> t`{.hyp} (Hyt) and `x /\ y`{.hyp} (H0). Going back to the definition of *and*{.just} (*match*{.just}) in *H0*{.just}, we prove `z /\ t`{.claim}:
    - ✅ Assume `x`{.hyp} (Hx) and `y`{.hyp} (Hy).
      - ✅ Applying *Hxz*{.just} to *Hx*{.just}, we have `z`{.claim}.
      - 🔶 **[1.1.1.2]** Prove `t`{.goal}.

        <details><summary>open goal of the text, not tried: condition 1.1.1.2, to prove in the Proof block: t</summary></details>


      So by definition of and (*conj*{.just}), we have `z /\ t`{.claim}.
