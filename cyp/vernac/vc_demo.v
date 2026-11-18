(* A text as a verification condition generator: the conditions cyp does
   not discharge are the goals of the Proof block, in the order of the
   text; each is named after its condition (?c1a for 1a, ?c2_1b for
   2.1b), and the script proves it by that name, in any order. *)
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
  [c1b]: apply Z.sqrt_nonneg.
  [c1a]: { Show. apply Z.sqrt_nonneg. }
CypQed.
Print Assumptions sqrt_sq.
