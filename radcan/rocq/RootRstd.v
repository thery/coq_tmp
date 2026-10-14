(* RADCAN on the real numbers of Stdlib (Reals).                              *)
(* Rstruct.v (borrowed from mathcomp-analysis) makes Stdlib's R an rcfType,  *)
(* so rootR_posroot R applies. This file translates Stdlib notation into the *)
(* mathcomp one that the reification understands:                            *)
(*   Rplus Rmult Ropp Rminus pow  ->  + * - - ^+                             *)
(*   Rinv Rdiv                    ->  ^-1 /                                  *)
(*   IZR numerals                 ->  k%:R                                    *)
(*   sqrt a                       ->  rootR 2 a  (both are 0 when a < 0)     *)
(*   radcan_Rstd  == the rewriting step (no side condition)                  *)
(*   radcan_Rstd_back == translates a side condition back to Stdlib, for lra *)

From Stdlib Require Import BinNums BinPos BinInt Reals.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import Rstruct PosRoot PosRootFacts RootR Syntax.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Lemma RplusE (x y : R) : Rplus x y = x + y. Proof. by []. Qed.
Lemma RmultE (x y : R) : Rmult x y = x * y. Proof. by []. Qed.
Lemma RoppE (x : R) : Ropp x = - x. Proof. by []. Qed.
Lemma RminusE (x y : R) : Rminus x y = x - y. Proof. by []. Qed.

Lemma RinvE (x : R) : Rinv x = x^-1. Proof. by []. Qed.
Lemma RdivE (x y : R) : Rdiv x y = x / y. Proof. by []. Qed.

Lemma RpowE (x : R) n : pow x n = x ^+ n.
Proof. by elim: n => [|n IH] //=; rewrite exprS IH. Qed.

Lemma INRE n : INR n = n%:R.
Proof.
elim: n => [|n IH] //; rewrite S_INR IH -[(n.+1)%:R]natr1.
by [].
Qed.

Lemma IZR0E : IZR Z0 = 0. Proof. by []. Qed.

(* numerals become pos2F p, exactly the interpretation of RCst (Zpos p): *)
(* the reification check is then syntactic, p is never expanded in unary *)
Lemma IZR_posE p : IZR (Zpos p) = pos2F R p.
Proof. by rewrite /pos2F -INRE INR_IPR. Qed.

Lemma IZR_negE p : IZR (Zneg p) = - pos2F R p.
Proof. by rewrite -IZR_posE. Qed.

Lemma sqrtE (a : R) : sqrt a = rootR 2 a.
Proof.
have [a_ge0|a_lt0] := leP 0 a.
  rewrite -rootR_posrootE; symmetry; apply: proot_eq => //.
    by apply/RleP/sqrt_pos.
  by rewrite expr2 -RmultE sqrt_sqrt //; apply/RleP.
rewrite rootR_out; last by rewrite /= -ltNge.
by rewrite sqrt_neg_0 //; apply/RleP; rewrite le_eqVlt a_lt0 orbT.
Qed.

(* numerals last: rewriting operators after them would unfold them in unary *)
Ltac radcan_Rstd :=
  rewrite ?RplusE ?RmultE ?RminusE ?RoppE ?RdivE ?RinvE ?RpowE ?sqrtE;
  rewrite ?IZR0E ?IZR_posE ?IZR_negE.

(* back to Stdlib notation, so that the side conditions left by radcan can  *)
(* be closed by lra / nra                                                   *)
Lemma natRE n : (n%:R : R) = INR n. Proof. by rewrite INRE. Qed.

Ltac radcan_Rstd_back :=
  match goal with
  | |- is_true (_ <= _) => apply/RleP
  | |- is_true (_ < _) => apply/RltP
  | |- is_true (_ != _) => apply/eqP
  | _ => idtac
  end;
  rewrite -?RplusE -?RoppE -?RmultE -?RinvE -?RpowE ?natRE /INR;
  try change (@Algebra.zero _) with (IZR 0);
  try change (@GRing.one _) with (IZR 1).
