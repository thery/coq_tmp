(******************************************************************************)
(* OmegaRoot2: the index law of the roots of -1 of a negroot (PosRoot.v),     *)
(* true for the principal roots of C (instance rootC_cycroot C in CycC.v).    *)
(*                                                                            *)
(*   cycroot w  == wroot w (n * k) ^+ k = wroot w n  (0 < n, 0 < k), i.e.     *)
(*                 omega_(n k) ^+ k = omega_n                                 *)
(*   windex r   == the same law on proot r n (-1), the value of the atom      *)
(*                 omega_n of the normaliser (it does not depend on w)        *)
(*   cycroot_windex : cycroot w -> windex r                                   *)
(*   windex_lift, windex_div == the two rewrites used to merge omega atoms:   *)
(*                 omega_n ^+ e = omega_l ^+ (e * (l / n))   (n | l)          *)
(*                 omega_n ^+ k = omega_(n / g) ^+ (k / g)   (g | n, g | k)   *)
(*   sqrtroot w == sqrt 2, 3, 5 as sums of roots of -1 (Omega6):             *)
(*                 sqrt 2 = w4 - w4 ^+ 3,  sqrt 3 = w6 - w6 ^+ 5,             *)
(*                 sqrt 5 = 2 w5 - 2 w5 ^+ 4 - 1   (wn = wroot w n)           *)
(*                 (instance rootC_sqrtroot C in CycC.v)                      *)
(*   wsqrt r    == the same on proot r n (-1); sqrtroot_wsqrt                *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Record cycroot (F : numFieldType) (r : posroot F) (w : negroot r) : Prop :=
  CycRoot {
  wroot_index : forall n k, (0 < n)%N -> (0 < k)%N ->
    wroot w (n * k) ^+ k = wroot w n
}.

Definition windex (F : numFieldType) (r : posroot F) : Prop :=
  forall n k, (0 < n)%N -> (0 < k)%N ->
    proot r (n * k) (-1) ^+ k = proot r n (-1).

Lemma cycroot_windex (F : numFieldType) (r : posroot F) (w : negroot r) :
  cycroot w -> windex r.
Proof.
move=> [cy] n k n0 k0.
by rewrite -!(wrootE w) ?muln_gt0 ?n0 // cy.
Qed.

Section WIndex.

Variables (F : numFieldType) (r : posroot F).
Hypothesis hw : windex r.

Lemma windex_lift n l e : (0 < n)%N -> (0 < l)%N -> (n %| l)%N ->
  proot r n (-1) ^+ e = proot r l (-1) ^+ (e * (l %/ n)).
Proof.
move=> n0 l0 nl; have q0 : (0 < l %/ n)%N by rewrite divn_gt0 // dvdn_leq.
have E : proot r l (-1) ^+ (l %/ n) = proot r n (-1).
  by rewrite -{1}(divnK nl) mulnC hw.
by rewrite mulnC exprM E.
Qed.

Lemma windex_div n g k : (0 < n)%N -> (0 < g)%N -> (g %| n)%N ->
  (g %| k)%N -> proot r n (-1) ^+ k = proot r (n %/ g) (-1) ^+ (k %/ g).
Proof.
move=> n0 g0 gn gk; have q0 : (0 < n %/ g)%N by rewrite divn_gt0 // dvdn_leq.
have E : proot r n (-1) ^+ g = proot r (n %/ g) (-1).
  by rewrite -{1}(divnK gn) hw.
by rewrite -{1}(divnK gk) mulnC exprM E.
Qed.

End WIndex.

(* square roots as sums of roots of -1 (milestone Omega6) *)
Record sqrtroot (F : numFieldType) (r : posroot F) (w : negroot r) : Prop :=
  SqrtRoot {
  wsqrt2 : proot r 2 2 = wroot w 4 - wroot w 4 ^+ 3;
  wsqrt3 : proot r 2 3 = wroot w 6 - wroot w 6 ^+ 5;
  wsqrt5 : proot r 2 5 = 2 * wroot w 5 - 2 * wroot w 5 ^+ 4 - 1
}.

Definition wsqrt (F : numFieldType) (r : posroot F) : Prop :=
  [/\ proot r 2 2 = proot r 4 (-1) - proot r 4 (-1) ^+ 3,
      proot r 2 3 = proot r 6 (-1) - proot r 6 (-1) ^+ 5 &
      proot r 2 5 = 2 * proot r 5 (-1) - 2 * proot r 5 (-1) ^+ 4 - 1].

Lemma sqrtroot_wsqrt (F : numFieldType) (r : posroot F) (w : negroot r) :
  sqrtroot w -> wsqrt r.
Proof. by case; rewrite !(wrootE w). Qed.
