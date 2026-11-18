(* A text as a verification condition generator: the conditions cyp does
   not discharge are the goals of the Proof block, in the order of the
   text; each says its number (condition := "1a"). *)
From Stdlib Require Import ZArith Lia PrimString List.
From CypV Require Import Cyp.
Import ListNotations.
Open Scope Z_scope.
Open Scope pstring_scope.

(* the default tactics know nothing of Z.sqrt: 1a and 1b are left *)
Cyp Lemma sqrt_sq (a b : Z) (H : 0 <= a) (Hb : 0 <= b) :
  0 <= Z.sqrt a * Z.sqrt a + Z.sqrt b :=
  [ "We have" (0 <= Z.sqrt a) "and" (0 <= Z.sqrt b) ;
    "So" (0 <= Z.sqrt a * Z.sqrt a) ].
Proof.
  - Show. apply Z.sqrt_nonneg.
  - Show. apply Z.sqrt_nonneg.
CypQed.
Print Assumptions sqrt_sq.
