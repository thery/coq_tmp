---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: fr
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

✅ Soit `m : nat`{.var}. Montrons `m + 0 = m`{.claim}.

- ✅ Montrons `m + 0 = m` par récurrence sur *m*{.just} (*nat*{.just}, *induction*{.just}):
  - ✅ Cas 1 (base): montrons `0 + 0 = 0 + 0`{.claim}.
    - ✅ Par définition de eq (*eq_refl*{.just}), nous avons `0 + 0 = 0 + 0`{.claim}.
  - ✅ Cas 2 (inductif): montrons `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
    - ✅ Choisissons arbitrairement `m0 : nat`{.var}; supposons par hypothèse de récurrence `m0 + 0 = m0`{.hyp} (IH).
      - ▫️ L'élément `nat` appartient à `Type`.
      - ▫️ L'élément `nat` appartient à `Type`.
      - ▫️ L'élément `S` appartient à `nat -> nat`.
      - ▫️ L'élément `m0 + 0` appartient à `nat`.
      - ✅ Par *IH*{.just} nous avons `m0 + 0 = m0`{.claim}.

      En appliquant *f_equal*{.just}, nous avons `S (m0 + 0) = S m0`{.claim}.

  Ces cas étant exhaustifs, nous en déduisons `m + 0 = m`{.claim}.
