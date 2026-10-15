(******************************************************************************)
(* OmegaRoot: extra laws of the roots of -1 of a negroot (PosRoot.v), true    *)
(* for the principal roots of C (instances in OmegaC.v).                      *)
(*                                                                            *)
(*   smallroot w == the explicit values of wroot w n for 2n | 24, in terms of *)
(*                  wroot w 2 (= 'i on C) and the square roots proot r 2 k:   *)
(*                    wroot w 3  = (1 + sqrt 3 * w2) / 2                      *)
(*                    wroot w 4  = sqrt 2 / 2 * (1 + w2)                      *)
(*                    wroot w 6  = (sqrt 3 + w2) / 2                          *)
(*                    wroot w 12 = ((sqrt 6 + sqrt 2)                         *)
(*                                   + (sqrt 6 - sqrt 2) * w2) / 4            *)
(*                  (wroot w 1 = -1 holds for any negroot: wrootK)            *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Record smallroot (F : numFieldType) (r : posroot F) (w : negroot r) : Prop :=
  SmallRoot {
  wroot3 : wroot w 3 = (1 + proot r 2 3 * wroot w 2) / 2;
  wroot4 : wroot w 4 = proot r 2 2 / 2 * (1 + wroot w 2);
  wroot6 : wroot w 6 = (proot r 2 3 + wroot w 2) / 2;
  wroot12 : wroot w 12 = (proot r 2 6 + proot r 2 2
                          + (proot r 2 6 - proot r 2 2) * wroot w 2) / 4
}.

Lemma wroot1 (F : numFieldType) (r : posroot F) (w : negroot r) :
  wroot w 1 = -1.
Proof. by rewrite -[wroot w 1]expr1 wrootK. Qed.
