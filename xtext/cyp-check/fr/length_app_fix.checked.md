---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: fr
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# length_app'

✅ Montrons `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim}.

- ✅ Montrons `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim} par récursion sur `l1`{.fact} (fix length_app'):
  - ▫️ Soit `A : Type`{.var}.
  - ▫️ Soient `l1 l2 : list A`{.var}.
  - ▫️ Montrons `length (l1 ++ l2) = length l1 + length l2`{.fact} par récurrence sur `l1`{.fact} (list, match):
  - ✅ Cas 1 (base): montrons `length (nil ++ l2) = length (nil ++ l2)`{.claim}.
    - ✅ Par définition de eq (eq_refl), nous avons `length (nil ++ l2) = length (nil ++ l2)`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - ✅ Cas 2 (inductif): montrons `A -> forall l : list A, S (length (l ++ l2)) = S (length l + length l2)`{.claim}.
    - ▫️ Soit `x : A`{.var}.
    - ▫️ Soit `l : list A`{.var}.
    - ❌ Par hypothèse de récurrence (l'appel récursif length_app') nous avons `forall (A0 : Type) (l10 l20 : list A0), length (l10 ++ l20) = length l10 + length l20`{.claim}.

      <details><summary>not proved: forall (A0 : Type) (l10 l20 : list A0),
length (l10 ++ l20) = length l10 + length l20</summary></details>

    - ✅ En utilisant f_equal nous obtenons `forall (A0 B : Type) (f : A0 -> B) (x0 y : A0), x0 = y -> f x0 = f y`{.claim} *by Corelib.Init.Logic.f_equal*.
    - ✅ Nous en déduisons `S (length (l ++ l2)) = S (length l + length l2)`{.claim} *by congruence*.
  - ❌ Ces cas étant exhaustifs, nous en déduisons `length (l1 ++ l2) = length l1 + length l2`{.claim}.

    <details><summary>not proved: length (l1 ++ l2) = length l1 + length l2</summary></details>

