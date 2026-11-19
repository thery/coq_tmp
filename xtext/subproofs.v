(* Tests of the subproofs of the staged translation (Coscoy's thesis,
   4.3.2 and 4.3.3; elpi/subproofs.elpi): the selected term of a theorem
   (as in selection.v), with its translatable occurrences marked ♡
   (Fig. 4.12), then with its intermediate results named (Fig. 4.14).
   Each test fails if a printed term is not the expected one. *)
From XText Require Import ExtractText thesis.
From XText Extra Dependency "test-helpers.elpi" as test_helpers.
Elpi Accumulate ExtractText File test_helpers.

(* [check-naming Name Naming Marked Named] (for this file only): Naming is
   the value of the switch naming, all or shared *)
Elpi Accumulate ExtractText lp:{{
  pred check-naming i:string, i:string, i:string, i:string.
  check-naming Name Naming Marked Named :-
    with-switches (with-switch "naming" "the test" Naming
      (with-switch "selection" "the test" "thesis"
        (named-term Name M N))),
    expect "marked" Name Marked M,
    expect "named" Name Named N.

  pred named-term i:string, o:string, o:string.
  named-term Name M N :-
    coq.locate Name (const C), coq.env.const C (some Bo) Ty,
    annotate Bo Ty T, select T S,
    translatable S K, (show-translatable => aterm-string K M),
    name-subproofs S R, aterm-string R N.

  % [check-text Name Naming Lang Lines]: the text of Name in the language
  % Lang, from its statement on (the non-empty lines after the title)
  pred check-text i:string, i:string, i:string, i:list string.
  check-text Name Naming Lang Lines :-
    with-switches (with-switch "naming" "the test" Naming
      (with-switch "selection" "the test" "thesis"
        (with-switch "lang" "the test" Lang
          (expect-text Name Lines)))).
}}.

(* Fig. 4.27, the example ABCD (Fig. 4.22-4.30): every subproof is
   translatable; the three subproofs that keep a type are named in postfix
   order, P1 (h3 h4) inside P2, then P3 *)
Elpi Query ExtractText lp:{{ check-naming "ABCD" "all"
  "(λA:Prop. λB:Prop. λC:Prop. λD:Prop. λh1:A -> B -> C -> D. λh2:A -> C -> B. λh3:A -> C. λh4:A. ((h1♡ h4♡ ((h2♡ h4♡ ((h3♡ h4♡) : C)♡) : B)♡ ((h3♡ h4♡) : C)♡) : D)♡ : forall A B C D : Prop, (A -> B -> C -> D) -> (A -> C -> B) -> (A -> C) -> A -> D)"
  "(λA:Prop. λB:Prop. λC:Prop. λD:Prop. λh1:A -> B -> C -> D. λh2:A -> C -> B. λh3:A -> C. λh4:A. let P1 : C = (h3 h4) in let P2 : B = (h2 h4 P1) in let P3 : C = (h3 h4) in ((h1 h4 P2 P3) : D) : forall A B C D : Prop, (A -> B -> C -> D) -> (A -> C -> B) -> (A -> C) -> A -> D)" }}.

(* Fig. 4.17: P3 proves C, which P1 already proves: P1 is used *)
Elpi Query ExtractText lp:{{ check-naming "ABCD" "shared"
  "(λA:Prop. λB:Prop. λC:Prop. λD:Prop. λh1:A -> B -> C -> D. λh2:A -> C -> B. λh3:A -> C. λh4:A. ((h1♡ h4♡ ((h2♡ h4♡ ((h3♡ h4♡) : C)♡) : B)♡ ((h3♡ h4♡) : C)♡) : D)♡ : forall A B C D : Prop, (A -> B -> C -> D) -> (A -> C -> B) -> (A -> C) -> A -> D)"
  "(λA:Prop. λB:Prop. λC:Prop. λD:Prop. λh1:A -> B -> C -> D. λh2:A -> C -> B. λh3:A -> C. λh4:A. let P1 : C = (h3 h4) in let P2 : B = (h2 h4 P1) in ((h1 h4 P2 P1) : D) : forall A B C D : Prop, (A -> B -> C -> D) -> (A -> C -> B) -> (A -> C) -> A -> D)" }}.

(* Argument of application (Fig. 4.12): f's type depends on its argument,
   so the proof (g b) is not translatable: it is written as a term, and
   not named (let P1 : A = g b in f P1 would prove P P1, not P (g b):
   4.3.3, "β-expansion et types dépendants").  Argument of abstraction
   (Fig. 4.13): the statement depends on b, a proof of B, which is
   introduced as a variable, not as a hypothesis. *)
Definition dependent_argument : forall (A B : Prop) (P : A -> Prop) (g : B -> A) (b : B),
  (forall a : A, P a) -> P (g b) :=
  fun A B P g b f => f (g b).
Elpi Query ExtractText lp:{{ check-naming "dependent_argument" "all"
  "(λA:Prop. λB:Prop. λP:A -> Prop. λg:B -> A. λb:B. λf:forall a : A, P a. ((f♡ (g b : A)) : P (g b))♡ : forall (A B : Prop) (P : A -> Prop) (g : B -> A) (b : B), (forall a : A, P a) -> P (g b))"
  "(λA:Prop. λB:Prop. λP:A -> Prop. λg:B -> A. λb:B. λf:forall a : A, P a. ((f (g b : A)) : P (g b)) : forall (A B : Prop) (P : A -> Prop) (g : B -> A) (b : B), (forall a : A, P a) -> P (g b))" }}.

(* The text of dependent_argument: g and b are variables (Fig. 4.13), g b
   an element (Fig. 4.12) *)
Elpi Query ExtractText lp:{{ check-text "dependent_argument" "all" "en" [
  "Let `A B : Prop`{.var}. Let `P : A -> Prop`{.var}. Let `g : B -> A`{.var}. Let `b : B`{.var}. Assume `forall a : A, P a`{.hyp} (f). We prove `P (g b)`{.claim}.",
  "- The element `g b` belongs to `A`.",
  "- Applying *f*{.just}, we have `P (g b)`{.claim}."] }}.

(* Fig. 4.30, the text of ABCD in French (the thesis's language; the
   thesis writes "Preuve P1 : montrons C. Nous appliquons h3 à h4. Fin
   de P1.", the text here a step whose claim is named, (P1)), and in
   English *)
Elpi Query ExtractText lp:{{ check-text "ABCD" "all" "fr" [
  "Soient `A B C D : Prop`{.var}. Supposons `A -> B -> C -> D`{.hyp} (h1), `A -> C -> B`{.hyp} (h2), `A -> C`{.hyp} (h3) et `A`{.hyp} (h4). Montrons `D`{.claim}.",
  "- En appliquant *h3*{.just} à *h4*{.just}, nous avons `C`{.claim} (P1).",
  "- En appliquant *h2*{.just} à *h4*{.just} et *P1*{.just}, nous avons `B`{.claim} (P2).",
  "- En appliquant *h3*{.just} à *h4*{.just}, nous avons `C`{.claim} (P3).",
  "- En appliquant *h1*{.just} à *h4*{.just}, *P2*{.just} et *P3*{.just}, nous avons `D`{.claim}."] }}.
Elpi Query ExtractText lp:{{ check-text "ABCD" "all" "en" [
  "Let `A B C D : Prop`{.var}. Assume `A -> B -> C -> D`{.hyp} (h1), `A -> C -> B`{.hyp} (h2), `A -> C`{.hyp} (h3) and `A`{.hyp} (h4). We prove `D`{.claim}.",
  "- Applying *h3*{.just} to *h4*{.just}, we have `C`{.claim} (P1).",
  "- Applying *h2*{.just} to *h4*{.just} and *P1*{.just}, we have `B`{.claim} (P2).",
  "- Applying *h3*{.just} to *h4*{.just}, we have `C`{.claim} (P3).",
  "- Applying *h1*{.just} to *h4*{.just}, *P2*{.just} and *P3*{.just}, we have `D`{.claim}."] }}.

(* Fig. 4.17, the text of ABCD with a result proved once per type *)
Elpi Query ExtractText lp:{{ check-text "ABCD" "shared" "en" [
  "Let `A B C D : Prop`{.var}. Assume `A -> B -> C -> D`{.hyp} (h1), `A -> C -> B`{.hyp} (h2), `A -> C`{.hyp} (h3) and `A`{.hyp} (h4). We prove `D`{.claim}.",
  "- Applying *h3*{.just} to *h4*{.just}, we have `C`{.claim} (P1).",
  "- Applying *h2*{.just} to *h4*{.just} and *P1*{.just}, we have `B`{.claim} (P2).",
  "- Applying *h1*{.just} to *h4*{.just}, *P2*{.just} and *P1*{.just}, we have `D`{.claim}."] }}.

(* A named abstraction (rule Abs of Fig. 4.14): its results are numbered
   after its own name, P1.1, and stay under its binder *)
Definition named_abstraction : forall A B C D : Prop,
  ((A -> C) -> D) -> (B -> C) -> (A -> B) -> D :=
  fun A B C D h k g => h (fun a => k (g a)).
Elpi Query ExtractText lp:{{ check-naming "named_abstraction" "all"
  "(λA:Prop. λB:Prop. λC:Prop. λD:Prop. λh:(A -> C) -> D. λk:B -> C. λg:A -> B. ((h♡ (λa:A. ((k♡ ((g♡ a♡) : B)♡) : C)♡ : A -> C)) : D)♡ : forall A B C D : Prop, ((A -> C) -> D) -> (B -> C) -> (A -> B) -> D)"
  "(λA:Prop. λB:Prop. λC:Prop. λD:Prop. λh:(A -> C) -> D. λk:B -> C. λg:A -> B. let P1 : A -> C = λa:A. let P1.1 : B = (g a) in ((k P1.1) : C) in ((h P1) : D) : forall A B C D : Prop, ((A -> C) -> D) -> (B -> C) -> (A -> B) -> D)" }}.
Elpi Query ExtractText lp:{{ check-text "named_abstraction" "all" "en" [
  "Let `A B C D : Prop`{.var}. Assume `(A -> C) -> D`{.hyp} (h), `B -> C`{.hyp} (k) and `A -> B`{.hyp} (g). We prove `D`{.claim}.",
  "- We have proved `A -> C`{.claim} (P1).",
  "  - Assume `A`{.hyp} (a).",
  "    - Applying *g*{.just} to *a*{.just}, we have `B`{.claim} (P1.1).",
  "    Applying *k*{.just} to P1.1, we have `C`{.claim}.",
  "- Applying *h*{.just} to *P1*{.just}, we have `D`{.claim}."] }}.

(* A form of the direct writer inside an application (a case analysis):
   the results of its cases are numbered after the next index, P1.1 *)
Definition nested_cases : forall A B C D E : Prop,
  A \/ B -> (A -> E) -> (E -> C) -> (B -> C) -> (C -> D) -> D :=
  fun A B C D E hab u f g k =>
    k (match hab with or_introl a => f (u a) | or_intror b => g b end).
Elpi Query ExtractText lp:{{ check-text "nested_cases" "all" "en" [
  "Let `A B C D E : Prop`{.var}. Assume `A \\/ B`{.hyp} (hab), `A -> E`{.hyp} (u), `E -> C`{.hyp} (f), `B -> C`{.hyp} (g) and `C -> D`{.hyp} (k). We prove `D`{.claim}.",
  "- We prove `C` by case analysis on *hab*{.just} (*or*{.just}, *match*{.just}):",
  "  - Case 1: we prove `A -> C`{.claim}.",
  "    - Assume `A`{.hyp} (a).",
  "      - Applying *u*{.just} to *a*{.just}, we have `E`{.claim} (P1.1).",
  "      Applying *f*{.just} to P1.1, we have `C`{.claim}.",
  "  - Case 2: we prove `B -> C`{.claim}.",
  "    - Assume `B`{.hyp} (b). Applying *g*{.just} to *b*{.just}, we have `C`{.claim}.",
  "  We have `C`{.claim} in all cases.",
  "- Applying *k*{.just}, we have `D`{.claim}."] }}.
