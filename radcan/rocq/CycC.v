(******************************************************************************)
(* CycC: the index law of the principal roots of -1 on C (milestone Omega4).  *)
(* rootC_N1_index is the index law of UnitArc.v (Omega3).                     *)
(*   rootC_cycroot C : cycroot (rootC_negroot C)   (OmegaRoot2.v)             *)
(*   radcan_eq_cond_rootC_negc, radcan_eq_refined_rootC_negc : the decision  *)
(*      theorems of radcan_check_negc on n.-root goals                        *)
(*   omega6_sqrt3C   : omega_6 - omega_6 ^+ 5 = sqrtC 3                       *)
(*   omega5_sqrt5C   : 2 omega_5 - 2 omega_5 ^+ 4 - 1 = sqrtC 5 (the sign:    *)
(*                     0 <= 'Re omega_5, by the maximality of 'Re omega_5     *)
(*                     among the 10-th roots of unity, UnitArc.v)             *)
(*   rootC_sqrtroot C : sqrtroot (rootC_negroot C)   (OmegaRoot2.v)           *)
(*   radcan_eq_cond_rootC_negs, radcan_eq_refined_rootC_negs : the same for   *)
(*      radcan_check_negs (Omega6)                                            *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot RootC Syntax Radcan Refine OmegaRoot2.
From Radcan Require Import NegCyc OmegaC UnitArc.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section CycC.

Variable C : numClosedFieldType.

(* wroot (rootC_negroot C) n is n.-root (-1) by conversion *)
Lemma rootC_cycroot : cycroot (rootC_negroot C).
Proof. by split=> n k n0 k0; exact: rootC_N1_index. Qed.

Theorem radcan_eq_cond_rootC_negc (env : seq C) e1 e2 cs :
  radcan_check_negc e1 e2 = Some cs -> all_conds (rootC_posroot C) env cs ->
  rinterp (rootC_posroot C) env e1 = rinterp (rootC_posroot C) env e2.
Proof. exact: (radcan_eq_cond_negc rootC_cycroot). Qed.

Theorem radcan_eq_refined_rootC_negc (env : seq C) e1 e2 cs rcs :
  radcan_check_negc e1 e2 = Some cs -> refine cs = rcs ->
  all_rconds C (proot (rootC_posroot C)) env rcs ->
  rinterp (rootC_posroot C) env e1 = rinterp (rootC_posroot C) env e2.
Proof. exact: (radcan_eq_refined_negc rootC_cycroot). Qed.

(* Omega6: square roots as sums of roots of -1 *)

Lemma omega6_sqrt3C : 6.-root (-1 : C) - 6.-root (-1) ^+ 5 = sqrtC 3.
Proof.
rewrite -[5%N]/(3 + 2)%N exprD omega6_cubeC omega6_sqrC omega6C omega3C.
rewrite mulrA.
have -> : 'i * (1 + sqrtC 3 * 'i) = 'i - sqrtC 3 :> C.
  by rewrite mulrDr mulr1 mulrCA -expr2 sqrCi mulrN1.
rewrite -mulrBl opprB addrC addrA (addrAC (sqrtC 3)) subrK -mulr2n.
by rewrite -[sqrtC 3 *+ 2]mulr_natr mulfK // pnatr_eq0.
Qed.

(* polynomial identities, checked by the root-free normaliser *)
Lemma phi10_factor (z : C) :
  (z + 1) * (z ^+ 4 - z ^+ 3 + z ^+ 2 - z + 1) = z ^+ 5 + 1.
Proof.
pose x := RVar 0.
have := @radcan_eq_cond0 C [:: z]
  (RMul (RAdd x (RCst 1))
        (RAdd (RSub (RAdd (RSub (RPow x 4) (RPow x 3)) (RPow x 2)) x)
              (RCst 1)))
  (RAdd (RPow x 5) (RCst 1)) [::] erefl erefl.
by move=> /(_ erefl I) /=; rewrite pos2F1.
Qed.

Lemma sqrt5_poly (z : C) : (2 * (z - z ^+ 4) - 1) ^+ 2 =
  4 * ((z ^+ 4 - z ^+ 3 + z ^+ 2 - z + 1) + (z ^+ 3 - 2) * (z ^+ 5 + 1))
  + 5.
Proof.
pose x := RVar 0.
have := @radcan_eq_cond0 C [:: z]
  (RPow (RSub (RMul (RCst 2) (RSub x (RPow x 4))) (RCst 1)) 2)
  (RAdd (RMul (RCst 4)
     (RAdd (RAdd (RSub (RAdd (RSub (RPow x 4) (RPow x 3)) (RPow x 2)) x)
                 (RCst 1))
           (RMul (RSub (RPow x 3) (RCst 2)) (RAdd (RPow x 5) (RCst 1)))))
     (RCst 5)) [::] erefl erefl.
by move=> /(_ erefl I) /=; rewrite pos2F1.
Qed.

Lemma omega5_sqrt5C :
  2 * 5.-root (-1 : C) - 2 * 5.-root (-1) ^+ 4 - 1 = sqrtC 5.
Proof.
set z := 5.-root (-1 : C).
have z5 : z ^+ 5 = -1 by rewrite rootCK.
have Iz : 0 < 'Im z := @Im_rootC_N1_gt0 C 5 isT.
have z1 : z + 1 != 0.
  rewrite addr_eq0; apply: contraTneq Iz => ->.
  by rewrite raddfN /= (Creal_ImP _ (real1 C)) oppr0 ltxx.
have Phi : z ^+ 4 - z ^+ 3 + z ^+ 2 - z + 1 = 0.
  apply/eqP; have := phi10_factor z; rewrite z5 addNr => /eqP.
  by rewrite mulf_eq0 (negbTE z1).
have y2 : (2 * (z - z ^+ 4) - 1) ^+ 2 = 5.
  by rewrite sqrt5_poly Phi z5 addNr mulr0 addr0 mulr0 add0r.
have z10 : z ^+ (2 * 5) = 1 by rewrite mulnC exprM z5 sqrrN expr1n.
have zc : z^* * z = 1 := @unity_conj C (2 * 5) z isT z10.
have z4 : z ^+ 4 = - z^*.
  apply: (mulIf (_ : z != 0)); last by rewrite -exprSr z5 mulNr zc.
  by apply: contraTneq Iz => ->; rewrite (Creal_ImP _ (real0 C)) ltxx.
(* -conj z is a 10-th root of unity: its real part is at most 'Re z *)
have Rz : 0 <= 'Re z.
  have : 'Re (- z^*) <= 'Re z.
    apply: rootC_N1_max => //.
    - by rewrite exprNn -rmorphXn z10 rmorph1 mulr1 exprM sqrrN !expr1n.
    - by rewrite raddfN /= Im_conj opprK ltW.
    apply/eqP => E; move: Iz.
    have -> : z = -1 by rewrite -[z]conjCK -[z^*]opprK E rmorphN rmorph1.
    by rewrite raddfN /= (Creal_ImP _ (real1 C)) oppr0 ltxx.
  by rewrite raddfN /= Re_conj lerNl -subr_ge0 opprK -mulr2n pmulrn_lge0.
have Ex : z - z ^+ 4 = 'Re z * 2 by rewrite z4 opprK ReE mulfVK ?pnatr_eq0.
rewrite -mulrBr -y2; symmetry; apply: sqrCK; move: y2; rewrite Ex.
set y := 2 * ('Re z * 2) - 1 => y2.
have y1 : 0 <= y + 1 by rewrite subrK mulr_ge0 ?mulr_ge0.
have yy : (y + 1) * (y - 1) = 4.
  rewrite mulrC -subr_sqr y2 expr1n.
  by apply/eqP; rewrite subr_eq (natrD _ 4 1).
have y10 : 0 < y + 1.
  rewrite lt_def y1 andbT; apply: contra_eq_neq yy => ->.
  by rewrite mul0r eq_sym pnatr_eq0.
have : 0 < y - 1 by rewrite -(pmulr_rgt0 _ y10) yy ltr0n.
by rewrite subr_gt0 => /(lt_trans ltr01) /ltW.
Qed.

Lemma rootC_sqrtroot : sqrtroot (rootC_negroot C).
Proof.
split=> /=; first by rewrite omega4_sqrt2C.
  by rewrite omega6_sqrt3C.
by rewrite omega5_sqrt5C.
Qed.

Theorem radcan_eq_cond_rootC_negs (env : seq C) e1 e2 cs :
  radcan_check_negs e1 e2 = Some cs -> all_conds (rootC_posroot C) env cs ->
  rinterp (rootC_posroot C) env e1 = rinterp (rootC_posroot C) env e2.
Proof. exact: (radcan_eq_cond_negs rootC_cycroot rootC_sqrtroot). Qed.

Theorem radcan_eq_refined_rootC_negs (env : seq C) e1 e2 cs rcs :
  radcan_check_negs e1 e2 = Some cs -> refine cs = rcs ->
  all_rconds C (proot (rootC_posroot C)) env rcs ->
  rinterp (rootC_posroot C) env e1 = rinterp (rootC_posroot C) env e2.
Proof. exact: (radcan_eq_refined_negs rootC_cycroot rootC_sqrtroot). Qed.

End CycC.
