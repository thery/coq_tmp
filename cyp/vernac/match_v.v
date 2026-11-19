(* The fixed justifications *match*{.just} and *induction*{.just}, with
   the type of the object, *and*{.just}, *nat*{.just}; their errors (an
   object of another type, a type with no method, no object): the node is
   left as a goal. *)
From Stdlib Require Import PrimString List Lia.
From CypV Require Import Cyp.
Import ListNotations.
Open Scope pstring_scope.

(* the conditions closed only after the case analysis (no gap tactic) *)
#[gaps="off"]
Cyp Lemma and_swap_v (A B : Prop) (h : A /\ B) : B /\ A :=
  [ "Going back to the definition of *and*{.just} (*match*{.just}) in *h*{.just}, we have" (B /\ A) "{.claim}." ].
Proof. CypQed.

(* no object named: the one hypothesis of type and *)
#[gaps="off"]
Cyp Lemma and_swap_type (A B : Prop) (h : A /\ B) : B /\ A :=
  [ "By *match*{.just} on the conjunction (*and*{.just}), we have" (B /\ A) "{.claim}." ].
Proof. CypQed.

(* an induction on the variable n *)
#[gaps="off"]
Cyp Lemma add_0_v (n : nat) : n + 0 = n :=
  [ "By *induction*{.just} on *n*{.just} (*nat*{.just}), we have" (n + 0 = n) "{.claim}"
      [ "We have" (0 + 0 = 0) "{.claim}." ;
        "We have" (forall m, m + 0 = m -> S m + 0 = S m) "{.claim}." ] ].
Proof. CypQed.

(* errors: h is not of type or; a type alone; match with nothing named;
   each node is left as a goal of the Proof block *)
Cyp Lemma errors_m (A B : Prop) (h : A /\ B) (k : A /\ B) : B /\ A :=
  [ "By *match*{.just} on *h*{.just} (*or*{.just}), we have" (B /\ A) "{.claim}." ;
    "By *and*{.just} we have" (A /\ B) "{.claim}." ;
    "By *match*{.just} we have" (B /\ B) "{.claim}." ;
    "By *match*{.just} (*and*{.just}) we have" (A /\ A) "{.claim}." ].
Proof.
  Show.
  [c1]: tauto.
  [c2]: tauto.
  [c3]: tauto.
  [c4]: tauto.
CypQed.
