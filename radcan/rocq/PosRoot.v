(******************************************************************************)
(* PosRoot: the n-th root interface shared by the R and C instances.          *)
(*                                                                            *)
(*   posroot F == record of a root function proot : nat -> F -> F on a        *)
(*                numFieldType F, specified for 0 < n and 0 <= a              *)
(*   oddroot r == odd roots of negatives: proot r n (- a) = - proot r n a     *)
(*                (instance on rcfType in RootR.v, none on C)                 *)
(*   negroot r == roots of negatives through wroot n, an n-th root of -1:     *)
(*                proot r n (- a) = proot r n a * wroot n                     *)
(*                (instance on C in RootC.v, none on a real field)            *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Record posroot (F : numFieldType) := PosRoot {
  proot : nat -> F -> F;
  proot_ge0 : forall n a, (0 < n)%N -> 0 <= a -> 0 <= proot n a;
  prootK : forall n a, (0 < n)%N -> 0 <= a -> proot n a ^+ n = a;
  prootM : forall n a b, (0 < n)%N -> 0 <= a -> 0 <= b ->
    proot n (a * b) = proot n a * proot n b
}.

(* On a realFieldType it suffices to check 0 <= a (oddroot_ge0). *)
Record oddroot (F : numFieldType) (r : posroot F) : Prop := OddRoot {
  prootN : forall n a, odd n -> proot r n (- a) = - proot r n a
}.

(* wroot n is the paper's omega_n. *)
Record negroot (F : numFieldType) (r : posroot F) := NegRoot {
  wroot : nat -> F;
  prootNw : forall n a, (0 < n)%N -> 0 <= a ->
    proot r n (- a) = proot r n a * wroot n;
  wrootK : forall n, (0 < n)%N -> wroot n ^+ n = -1
}.
