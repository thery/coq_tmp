(* Tests of the implicit arguments of eliminations (Coscoy's thesis,
   6.4.1; elpi/applications.elpi, instance-without-motive): a dependent
   elimination of x0 that proves (P x0) is written "We prove (P x0) by
   cases on x0", without its generalised statement P, when P is found
   again from (P x0) and x0, by abstracting x0 (and the indices) in
   (P x0), as Rocq's elim does; else the text generalises (P x0) first
   (6.3.3).  The examples are the schemes of 6.3.3 and 6.3.4 (booleans,
   pairs, lists), a lemma of lemmas.v, and a motive that is not found.
   Each test fails if a text is not the expected one. *)
From XText Require Import ExtractText lemmas.
From XText Extra Dependency "test-helpers.elpi" as test_helpers.
Elpi Accumulate ExtractText File test_helpers.

(* [check-text Name Lang Lines] (for this file only): the text of Name in
   the language Lang, from its statement on (the non-empty lines after
   the title) *)
Elpi Accumulate ExtractText lp:{{
  pred check-text i:string, i:string, i:list string.
  check-text Name Lang Lines :-
    with-switches (with-switch "lang" "the test" Lang
      (expect-text Name Lines)).
}}.

(* 6.3.3, the booleans: "Pour montrer (P b0), par une preuve par cas,
   généralisons en λb:bool.(P b) avant de le spécialiser à b0", which
   6.4.1 lightens to "Montrons (P b0) par une preuve par cas sur b0" *)
Definition bool_P (P : bool -> Prop) (ht : P true) (hf : P false) (b0 : bool) : P b0 :=
  bool_ind P ht hf b0.
Time ExtractText bool_P to "examples/bool_P.md".
Elpi Query ExtractText lp:{{ check-text "bool_P" "fr" [
  "Soit `P : bool -> Prop`{.var}. Supposons `P true`{.hyp} (ht) et `P false`{.hyp} (hf). Soit `b0 : bool`{.var}. Montrons `P b0`{.claim}.",
  "- Montrons `P b0` par analyse de cas sur *b0*{.just} (*bool*{.just}, *match*{.just}):",
  "  - Cas 1: montrons `P true`{.claim}.",
  "    - Par *ht*{.just} nous avons `P true`{.claim}.",
  "  - Cas 2: montrons `P false`{.claim}.",
  "    - Par *hf*{.just} nous avons `P false`{.claim}.",
  "  Ces cas étant exhaustifs, nous en déduisons `P b0`{.claim}."] }}.

(* 6.3.3, the cartesian product, an elimination with one case: "Pour
   montrer (P p0), généralisons le en λp:(prod E F).(P p), avant de le
   spécialiser à p0", here without the generalisation *)
Definition prod_P (E F : Set) (P : prod E F -> Prop)
  (h : forall (x : E) (y : F), P (pair x y)) (p0 : prod E F) : P p0 :=
  prod_ind P h p0.
Time ExtractText prod_P to "examples/prod_P.md".
Elpi Query ExtractText lp:{{ check-text "prod_P" "fr" [
  "Soient `E F : Set`{.var}. Soit `P : E * F -> Prop`{.var}. Supposons `forall (x : E) (y : F), P (x, y)`{.hyp} (h). Soit `p0 : (E * F)%type`{.var}. Montrons `P p0`{.claim}.",
  "- Par définition de *prod*{.just} (*match*{.just}) sur *p0*{.just}, montrons `P p0`{.claim}:",
  "  - Par *h*{.just} nous avons `forall (x : E) (y : F), P (x, y)`{.claim}."] }}.

(* 6.3.4, the lists, by induction: "Pour montrer (P l0) par récurrence,
   généralisons en λl:(list E).(P l) avant de le spécialiser à l0", here
   "Montrons (P l0) par récurrence sur l0" *)
Definition list_P (E : Set) (P : list E -> Prop) (h0 : P nil)
  (h1 : forall x l, P l -> P (cons x l)) (l0 : list E) : P l0 :=
  list_ind P h0 h1 l0.
Time ExtractText list_P to "examples/list_P.md".
Elpi Query ExtractText lp:{{ check-text "list_P" "fr" [
  "Soit `E : Set`{.var}. Soit `P : list E -> Prop`{.var}. Supposons `P nil`{.hyp} (h0) et `forall (x : E) (l : list E), P l -> P (x :: l)%list`{.hyp} (h1). Soit `l0 : list E`{.var}. Montrons `P l0`{.claim}.",
  "- Montrons `P l0` par récurrence sur *l0*{.just} (*list*{.just}, *induction*{.just}):",
  "  - Cas 1 (base): montrons `P nil`{.claim}.",
  "    - Par *h0*{.just} nous avons `P nil`{.claim}.",
  "  - Cas 2 (inductif): montrons `forall (x : E) (l : list E), P l -> P (x :: l)%list`{.claim}.",
  "    - Par *h1*{.just} nous avons `forall (x : E) (l : list E), P l -> P (x :: l)%list`{.claim}.",
  "  Ces cas étant exhaustifs, nous en déduisons `P l0`{.claim}."] }}.
Elpi Query ExtractText lp:{{ check-text "list_P" "en" [
  "Let `E : Set`{.var}. Let `P : list E -> Prop`{.var}. Assume `P nil`{.hyp} (h0) and `forall (x : E) (l : list E), P l -> P (x :: l)%list`{.hyp} (h1). Let `l0 : list E`{.var}. We prove `P l0`{.claim}.",
  "- We prove `P l0` by induction on *l0*{.just} (*list*{.just}, *induction*{.just}):",
  "  - Case 1 (base): we prove `P nil`{.claim}.",
  "    - By *h0*{.just} we have `P nil`{.claim}.",
  "  - Case 2 (inductive): we prove `forall (x : E) (l : list E), P l -> P (x :: l)%list`{.claim}.",
  "    - By *h1*{.just} we have `forall (x : E) (l : list E), P l -> P (x :: l)%list`{.claim}.",
  "  These cases being exhaustive, we deduce `P l0`{.claim}."] }}.

(* add_0_r' (lemmas.v): the motive fun n0 => n0 + 0 = n0 is n abstracted
   in n + 0 = n, as elim finds it; the text proves n + 0 = n by
   induction on n *)
Elpi Query ExtractText lp:{{ check-text "add_0_r'" "en" [
  "Let `n : nat`{.var}. We prove `n + 0 = n`{.claim}.",
  "- We prove `n + 0 = n` by induction on *n*{.just} (*nat*{.just}, *induction*{.just}):",
  "  - Case 1 (base): we prove `0 = 0`{.claim}.",
  "    - By definition of eq (*eq_refl*{.just}), we have `0 = 0`{.claim}.",
  "  - Case 2 (inductive): we prove `forall m : nat, m + 0 = m -> S m + 0 = S m`{.claim}.",
  "    - Let us choose arbitrarily `m : nat`{.var}; assume by induction hypothesis `m + 0 = m`{.hyp} (IH).",
  "      - By definition of eq (*eq_refl*{.just}), we have `S m = S m`{.claim}.",
  "      - By *IH*{.just} we have `m + 0 = m`{.claim}.",
  "      Rewriting with `m + 0 = m`{.fact} from right to left (eq_ind_r), we get `S (m + 0) = S m`{.claim}.",
  "  These cases being exhaustive, we deduce `n + 0 = n`{.claim}."] }}.

(* Where the motive stays: the motive fun m => m + 0 = n abstracts only
   one of the occurrences of n in n + 0 = n, so it is not found from the
   instance and n; the text keeps the generalisation of 6.3.3 *)
Definition partial_motive (n : nat) (h0 : 0 + 0 = n)
  (hS : forall m, m + 0 = n -> S m + 0 = n) : n + 0 = n :=
  nat_ind (fun m => m + 0 = n) h0 hS n.
Elpi Query ExtractText lp:{{ check-text "partial_motive" "en" [
  "Let `n : nat`{.var}. Assume `0 + 0 = n`{.hyp} (h0) and `forall m : nat, m + 0 = n -> S m + 0 = n`{.hyp} (hS). We prove `n + 0 = n`{.claim}.",
  "- To prove `n + 0 = n` by induction (nat, *nat_ind*{.just}), we generalise it to `forall n0 : nat, n0 + 0 = n`:",
  "  - Case 1 (base): we prove `0 + 0 = n`{.claim}.",
  "    - By *h0*{.just} we have `0 + 0 = n`{.claim}.",
  "  - Case 2 (inductive): we prove `forall m : nat, m + 0 = n -> S m + 0 = n`{.claim}.",
  "    - By *hS*{.just} we have `forall m : nat, m + 0 = n -> S m + 0 = n`{.claim}.",
  "  These cases being exhaustive, we deduce `forall n0 : nat, n0 + 0 = n`{.claim}.",
  "- In particular `n + 0 = n`{.claim}."] }}.
