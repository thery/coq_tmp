---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# in_map

✅ Let `A B : Type`{.var}. Let `f : A -> B`{.var}. Let `l : list A`{.var}. We prove `forall x : A, In x l -> In (f x) (map f l)`{.claim}.

- ✅ We prove `forall x : A, In x l -> In (f x) (map f l)` by induction on `l` (list, *list_ind*{.just}):
  - ✅ Case 1 (base): we prove `forall x : A, In x nil -> In x nil`{.claim}.
    - ✅ Let `x : A`{.var}; assume `In x nil`{.hyp} (H). By *H*{.just} we have `In x nil`{.claim}.
  - ✅ Case 2 (inductive): we prove `forall (a : A) (l0 : list A), (forall x : A, In x l0 -> In (f x) (map f l0)) -> forall x : A, In x (a :: l0) -> In (f x) (map f (a :: l0))`{.claim}.
    - ✅ Let `a : A`{.var} and `l0 : list A`{.var}; assume by induction hypothesis `forall x : A, In x l0 -> In (f x) (map f l0)`{.hyp} (IHl); let `x : A`{.var}; assume `In x (a :: l0)`{.hyp} (H). We prove `In (f x) (map f (a :: l0))` by case analysis on *H*{.just} (or, *or_ind*{.just}):
      - ✅ Case 2.1: we prove `a = x -> f a = f x \/ In (f x) (map f l0)`{.claim}.
        - ✅ Assume `a = x`{.hyp} (H0).
          - ✅ By definition of eq (*eq_refl*{.just}), we have `f x = f x`{.claim}.
          - ✅ By *H0*{.just} we have `a = x`{.claim}.
          - ✅ Rewriting with `a = x`{.fact} from right to left (eq_ind_r), we get `f a = f x`{.claim}.

          By definition of or (*or_introl*{.just}), we have `f a = f x \/ In (f x) (map f l0)`{.claim}.
      - ✅ Case 2.2: we prove `In x l0 -> f a = f x \/ In (f x) (map f l0)`{.claim}.
        - ✅ Assume `In x l0`{.hyp} (H0).
          - ✅ We have proved `(In x l0 -> In (f x) (map f l0)) -> In (f x) (map f l0)`{.claim}.
            - ✅ Assume `In x l0 -> In (f x) (map f l0)`{.hyp} (H00).
              - ✅ We have proved `In (f x) (map f l0) -> In (f x) (map f l0)`{.claim}.
                - ✅ Assume `In (f x) (map f l0)`{.hyp} (H01). By *H01*{.just} we have `In (f x) (map f l0)`{.claim}.
              - ✅ Applying *H00*{.just} to *H0*{.just}, we have `In (f x) (map f l0)`{.claim}.

              By application, we have `In (f x) (map f l0)`{.claim}.
          - ✅ Applying *IHl*{.just} to x, we have `In x l0 -> In (f x) (map f l0)`{.claim}.
          - ✅ By application, we have `In (f x) (map f l0)`{.claim}.

          By definition of or (*or_intror*{.just}), we have `f a = f x \/ In (f x) (map f l0)`{.claim}.

      We have `In (f x) (map f (a :: l0))`{.claim} in all cases.

  These cases being exhaustive, we deduce `forall x : A, In x l -> In (f x) (map f l)`{.claim}.
