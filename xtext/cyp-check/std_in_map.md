---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# in_map

Let `A B : Type`{.var}. Let `f : A -> B`{.var}. Let `l : list A`{.var}. We prove `forall x : A, In x l -> In (f x) (map f l)`{.claim}.

- To prove `forall x : A, In x l -> In (f x) (map f l)`{.fact} by induction (list, list_ind), we generalise it to `forall (l0 : list A) (x : A), In x l0 -> In (f x) (map f l0)`{.fact}:
- Case 1 (base): we prove `forall x : A, In x nil -> In x nil`{.claim}.
  - Let `x : A`{.var}.
  - Assume `In x nil`{.hyp} (H).
    - By H we have `In x nil`{.claim}.
- Case 2 (inductive): we prove `forall (a : A) (l0 : list A), (forall x : A, In x l0 -> In (f x) (map f l0)) -> forall x : A, In x (a :: l0) -> In (f x) (map f (a :: l0))`{.claim}.
  - Let `a : A`{.var}.
  - Let `l0 : list A`{.var}.
  - Assume by induction hypothesis `forall x : A, In x l0 -> In (f x) (map f l0)`{.hyp} (IHl).
    - Let `x : A`{.var}.
    - Assume `In x (a :: l0)`{.hyp} (H).
      - We prove `In (f x) (map f (a :: l0))`{.fact} by case analysis on `In x (a :: l0)`{.fact} (H) (or, or_ind):
      - Case 2.1: we prove `a = x -> f a = f x \/ In (f x) (map f l0)`{.claim}.
        - Assume `a = x`{.hyp} (H0).
          - By definition of eq (eq_refl), we have `f x = f x`{.claim} *by eapply @eq_refl; eauto*.
          - By H0 we have `a = x`{.claim}.
          - Rewriting with `a = x`{.fact} from right to left (eq_ind_r), we get `f a = f x`{.claim}.
          - By definition of or (or_introl), we have `f a = f x \/ In (f x) (map f l0)`{.claim} *by eapply @or_introl; eauto*.
      - Case 2.2: we prove `In x l0 -> f a = f x \/ In (f x) (map f l0)`{.claim}.
        - Assume `In x l0`{.hyp} (H0).
          - In particular `In x l0 -> In (f x) (map f l0)`{.claim}.
            - By IHl we have `forall x0 : A, In x0 l0 -> In (f x0) (map f l0)`{.claim}.
          - We have proved `(In x l0 -> In (f x) (map f l0)) -> In (f x) (map f l0)`{.claim}.
            - Assume `In x l0 -> In (f x) (map f l0)`{.hyp} (H00).
              - We deduce `In (f x) (map f l0)`{.claim}.
                - By H0 we have `In x l0`{.claim}.
                - By H00 we have `In x l0 -> In (f x) (map f l0)`{.claim}.
              - We have proved `In (f x) (map f l0) -> In (f x) (map f l0)`{.claim}.
                - Assume `In (f x) (map f l0)`{.hyp} (H01).
                  - By H01 we have `In (f x) (map f l0)`{.claim}.
              - We deduce `In (f x) (map f l0)`{.claim}.
          - We deduce `In (f x) (map f l0)`{.claim}.
          - By definition of or (or_intror), we have `f a = f x \/ In (f x) (map f l0)`{.claim} *by eapply @or_intror; eauto*.
      - We have `In (f x) (map f (a :: l0))`{.claim} in all cases *by eapply (@or_ind (a = x) (In x l0) (In (f x) (map f (a :: l0)))); cbv beta; eauto*.
- These cases being exhaustive, we deduce `forall (l0 : list A) (x : A), In x l0 -> In (f x) (map f l0)`{.claim} *by eapply (@list_ind (A) (fun l0 : list A => forall x : A, In x l0 -> In (f x) (map f l0))); cbv beta; eauto*.
- In particular `forall x : A, In x l -> In (f x) (map f l)`{.claim}.
