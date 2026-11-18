---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: fr
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum

✅ Soient `x y z t : Prop`{.var}. Supposons `(x -> z) /\ (y -> t)`{.hyp} (h1) et `x /\ y`{.hyp} (h2). Montrons `z /\ t`{.claim}.

- ✅ En revenant à la définition de and (and_ind) dans `(x -> z) /\ (y -> t)`{.fact} (h1), montrons `z /\ t`{.claim}:
  - ▫️ Supposons `x -> z`{.hyp} (i) et `y -> t`{.hyp} (j).
    - ✅ En revenant à la définition de and (and_ind) dans `x /\ y`{.fact} (h2), montrons `z /\ t`{.claim}:
      - ▫️ Supposons `x`{.hyp} (k) et `y`{.hyp} (l).
        - ✅ Nous en déduisons `z`{.claim}.
          - ✅ Par k nous avons `x`{.claim}.
          - ✅ Par i nous avons `x -> z`{.claim}.
        - ✅ Nous en déduisons `t`{.claim}.
          - ✅ Par l nous avons `y`{.claim}.
          - ✅ Par j nous avons `y -> t`{.claim}.
        - ✅ Donc par définition de and (conj), nous avons `z /\ t`{.claim} *by Corelib.Init.Logic.conj*.
