(* The interface shared by the R and C instances: an n-th root function     *)
(* on a numFieldType, specified only on nonnegative arguments.               *)
(*   proot n a == the n-th root of a; meaningful when 0 <= a and 0 < n       *)
(* Instances: RootC.v (numClosedFieldType, ssrnum's n.-root) and             *)
(*            RootR.v (rcfType, root built from poly_ivt).                    *)

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

(* Odd roots of negative numbers (milestone M6).  On a real closed field the *)
(* real odd root satisfies  proot n (- a) = - proot n a  (RootR.v); on C the  *)
(* principal root does not (3.-root (-8) is not -2), so there is no instance. *)
(* On a realFieldType it is enough to check the law for 0 <= a              *)
(* (oddroot_ge0 in PosRootFacts.v).                                           *)
Record oddroot (F : numFieldType) (r : posroot F) : Prop := OddRoot {
  prootN : forall n a, odd n -> proot r n (- a) = - proot r n a
}.

(* Roots of negative numbers through roots of unity (milestone M9).  w n is  *)
(* the paper's omega_n, an n-th root of -1, and the n-th root of a negative  *)
(* number - a is proot n a * w n.  On C with the principal roots n.-root,    *)
(* w n = n.-root (-1) (NegRootC.v).  There is no instance on a real field:  *)
(* -1 has no square root there.                                              *)
Record negroot (F : numFieldType) (r : posroot F) := NegRoot {
  wroot : nat -> F;
  prootNw : forall n a, (0 < n)%N -> 0 <= a -> proot r n (- a) = proot r n a * wroot n;
  wrootK : forall n, (0 < n)%N -> wroot n ^+ n = -1
}.
