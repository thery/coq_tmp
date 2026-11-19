---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: fr
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# length_app'

Montrons `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim}.

- Montrons `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim} par récursion sur `l1`{.fact} (fix length_app'):
  - Soit `A : Type`{.var} et `l1 l2 : list A`{.var}.
    - Montrons `length (l1 ++ l2) = length l1 + length l2`{.fact} par récurrence sur `l1`{.fact} (list, match):
    - Cas 1 (base): montrons `length (nil ++ l2) = length (nil ++ l2)`{.claim}.
      - Par définition de eq (eq_refl), nous avons `length (nil ++ l2) = length (nil ++ l2)`{.claim} *by Corelib.Init.Logic.eq_refl*.
    - Cas 2 (inductif): montrons `A -> forall l : list A, S (length (l ++ l2)) = S (length l + length l2)`{.claim}.
      - Soit `x : A`{.var} et `l : list A`{.var}.
        - L'élément `nat`{.fact} appartient à `Type`{.fact}.
        - L'élément `nat`{.fact} appartient à `Type`{.fact}.
        - L'élément `S`{.fact} appartient à `nat -> nat`{.fact}.
        - L'élément `length (l ++ l2)`{.fact} appartient à `nat`{.fact}.
        - L'élément `length l + length l2`{.fact} appartient à `nat`{.fact}.
        - En particulier `length (l ++ l2) = length l + length l2`{.claim}.
          - Par hypothèse de récurrence (l'appel récursif length_app') nous avons `forall (A0 : Type) (l10 l20 : list A0), length (l10 ++ l20) = length l10 + length l20`{.claim}.
        - En appliquant f_equal, nous avons `S (length (l ++ l2)) = S (length l + length l2)`{.claim}.
    - Ces cas étant exhaustifs, nous en déduisons `length (l1 ++ l2) = length l1 + length l2`{.claim}.
