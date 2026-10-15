(******************************************************************************)
(* RootRstd: RADCAN on the real numbers of Stdlib (Reals), through Rstruct.v  *)
(* and rootR_posroot R.  Translation of Stdlib notation into the mathcomp one *)
(* understood by the reification:                                             *)
(*   Rplus Rmult Ropp Rminus pow  ->  + * - - ^+                              *)
(*   Rinv Rdiv                    ->  ^-1 /                                   *)
(*   IZR numerals                 ->  pos2F R p (interpretation of RCst)      *)
(*   sqrt a                       ->  rootR 2 a  (both are 0 when a < 0)      *)
(*   radcan_Rstd      == the rewriting tactic (no side condition)             *)
(*   radcan_Rstd_back == back to Stdlib notation, to close conditions by lra  *)
(*   radcan_lra       == radcan_Rstd; radcan; lra on each side condition     *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt Reals Lra.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import Rstruct PosRoot PosRootFacts RootR Syntax Tactic.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Lemma RplusE (x y : R) : Rplus x y = x + y. Proof. by []. Qed.
Lemma RmultE (x y : R) : Rmult x y = x * y. Proof. by []. Qed.
Lemma RoppE (x : R) : Ropp x = - x. Proof. by []. Qed.
Lemma RminusE (x y : R) : Rminus x y = x - y. Proof. by []. Qed.

Lemma RabsE (x : R) : Rabs x = `|x|. Proof. by []. Qed.
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

(* pos2F p is the interpretation of RCst (Zpos p): reification stays
   syntactic and p is never expanded in unary *)
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
  rewrite ?RplusE ?RmultE ?RminusE ?RoppE ?RdivE ?RinvE ?RpowE ?RabsE ?sqrtE;
  rewrite ?IZR0E ?IZR_posE ?IZR_negE.

Lemma natRE n : (n%:R : R) = INR n. Proof. by rewrite INRE. Qed.

Ltac radcan_Rstd_back1 :=
  match goal with
  | |- is_true (_ <= _) => apply/RleP
  | |- is_true (_ < _) => apply/RltP
  | |- is_true (_ != _) => apply/eqP
  | _ => idtac
  end;
  rewrite -?RplusE -?RoppE -?RmultE -?RinvE -?RpowE -?RabsE ?natRE /INR;
  try change (@Algebra.zero _) with (IZR 0);
  try change (@GRing.one _) with (IZR 1).

(* an interval a <= x <= b is split in two goals *)
Ltac radcan_Rstd_back :=
  lazymatch goal with
  | |- is_true (_ && _) => apply/andP; split; radcan_Rstd_back
  | _ => radcan_Rstd_back1
  end.

(* radcan on a Stdlib goal; the side conditions that lra proves are closed, *)
(* the others are left in mathcomp notation                                 *)
Ltac radcan_lra := radcan_Rstd; radcan; try (radcan_Rstd_back; lra).
