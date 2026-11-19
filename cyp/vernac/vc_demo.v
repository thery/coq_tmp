(* A text as a verification condition generator: the conditions cyp does
   not discharge are the goals of the Proof block, in the order of the
   text; each is named after its node (?c1 for 1, ?c2_1 for 2.1), and the
   script proves it by that name, in any order. *)
From Stdlib Require Import ZArith Lia PrimString List.
From CypV Require Import Cyp.
Import ListNotations.
Open Scope Z_scope.
Open Scope pstring_scope.

(* the default tactics know nothing of Z.sqrt: 1 and 2 are left *)
Cyp Lemma sqrt_sq (a b : Z) (H : 0 <= a) (Hb : 0 <= b) :
  0 <= Z.sqrt a * Z.sqrt a + Z.sqrt b :=
  [ "We have" (0 <= Z.sqrt a) "{.claim}." ;
    "We have" (0 <= Z.sqrt b) "{.claim}." ;
    "So" (0 <= Z.sqrt a * Z.sqrt a) "{.claim}." ].
Proof.
  [c2]: apply Z.sqrt_nonneg.
  [c1]: { Show. apply Z.sqrt_nonneg. }
CypQed.
Print Assumptions sqrt_sq.
