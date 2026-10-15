(******************************************************************************)
(* OmegaC: mathcomp's principal roots on a numClosedFieldType C, and the      *)
(* explicit values of omega_n = n.-root (-1) for 2n | 24.                     *)
(*                                                                            *)
(*   rootC_char      : n.-root x is the root y of X^n - x with 0 <= 'Im y and *)
(*                     the largest real part among the roots in 0 <= 'Im      *)
(*   sqrtC_char      : sqrtC w = y when y ^+ 2 = w, 0 <= 'Im y and            *)
(*                     ('Im y = 0 -> 0 <= 'Re y); sqrtC_char_Im: 0 < 'Im y    *)
(*   rootC_double    : (2 * n).-root x = sqrtC (n.-root x)  (0 < n)           *)
(*   omega1C .. omega12C : omega_1 = -1, omega_2 = 'i,                        *)
(*                     omega_3 = (1 + sqrtC 3 * 'i) / 2,                      *)
(*                     omega_4 = sqrtC 2 / 2 * (1 + 'i),                      *)
(*                     omega_6 = (sqrtC 3 + 'i) / 2,                          *)
(*                     omega_12 = ((sqrtC 6 + sqrtC 2)                        *)
(*                                 + (sqrtC 6 - sqrtC 2) * 'i) / 4            *)
(*   omega3_cycloC   : omega_3 ^+ 2 - omega_3 + 1 = 0                         *)
(*   omega4_sqrt2C   : omega_4 - omega_4 ^+ 3 = sqrtC 2   (paper (2))         *)
(*   omega{4,6,12}_sqrC, omega{4,6,12}_cubeC, omega4_invC: squares, cubes     *)
(*   rootC_smallroot C : smallroot (rootC_negroot C)   (OmegaRoot.v)          *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot RootC OmegaRoot.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section RootChar.

Variable C : numClosedFieldType.

Lemma rootC_char n (x y : C) : (0 < n)%N -> y ^+ n = x -> 0 <= 'Im y ->
  (forall z, z ^+ n = x -> 0 <= 'Im z -> 'Re z <= 'Re y) -> n.-root x = y.
Proof.
move=> n0 yx Iy ymax.
case: n n0 yx ymax => // -[_ yx _|n _ yx ymax].
  by rewrite root1C -yx expr1.
have rx : n.+2.-root x ^+ n.+2 = x by rewrite rootCK.
have Ir : 0 <= 'Im (n.+2.-root x) by rewrite Im_rootC_ge0.
apply: eqC_semipolar.
- apply/eqP; rewrite -(eqrXn2 (isT : (0 < n.+2)%N)) ?normr_ge0 //.
  by rewrite -!normrX rx yx.
- by apply/le_anti; rewrite ymax //= rootC_Re_max.
- by rewrite mulr_ge0.
Qed.

Lemma sqrtC_char (w y : C) : y ^+ 2 = w -> 0 <= 'Im y ->
  ('Im y = 0 -> 0 <= 'Re y) -> sqrtC w = y.
Proof.
move=> yw Iy Ry; apply: rootC_char => // z; rewrite -yw => /eqP.
rewrite eqf_sqr => /orP[/eqP -> //|/eqP ->].
rewrite !raddfN /= oppr_ge0 => Iy0.
have /Ry Ry0 : 'Im y = 0 by apply/le_anti; rewrite Iy0.
by rewrite (le_trans _ Ry0) // oppr_le0.
Qed.

Lemma sqrtC_char_Im (w y : C) : y ^+ 2 = w -> 0 < 'Im y -> sqrtC w = y.
Proof.
move=> yw Iy; apply: sqrtC_char => //; first exact: ltW.
by move=> Iy0; rewrite Iy0 ltxx in Iy.
Qed.

Lemma Re_sqrtC_ge0 (w : C) : 0 <= 'Im w -> 0 <= 'Re (sqrtC w).
Proof.
set y := sqrtC w => Iw.
have Iy : 0 <= 'Im y by rewrite Im_rootC_ge0.
have [Iy0|Iy0] := eqVneq ('Im y) 0.
  have : 'Re (- y) <= 'Re (sqrtC w).
    by apply: rootC_Re_max; rewrite ?sqrrN ?sqrtCK // raddfN /= Iy0 oppr0.
  rewrite -/y raddfN /= lerNl -subr_ge0 opprK -mulr2n.
  by rewrite pmulrn_lge0.
have Iy1 : 0 < 'Im y by rewrite lt_def Iy0.
move: Iw; rewrite -[w]sqrtCK expr2 ImM -/y -mulr2n.
by rewrite pmulrn_lge0 // pmulr_lge0.
Qed.

Lemma rootC_double n (x : C) : (0 < n)%N ->
  (2 * n).-root x = sqrtC (n.-root x).
Proof.
case: n => // -[_|n _]; first by rewrite root1C.
set r := n.+2.-root x; set y := sqrtC r.
have rx : r ^+ n.+2 = x by rewrite rootCK.
have Ir : 0 <= 'Im r by rewrite Im_rootC_ge0.
have Ry : 0 <= 'Re y by rewrite Re_sqrtC_ge0.
have yx : y ^+ (2 * n.+2) = x by rewrite exprM sqrtCK.
apply: rootC_char => //; first by rewrite Im_rootC_ge0.
move=> z zx Iz.
have zy : `|z| = `|y|.
  apply/eqP; rewrite -(eqrXn2 (isT : (0 < 2 * n.+2)%N)) ?normr_ge0 //.
  by rewrite -!normrX zx yx.
have ReIm (u : C) : 'Re (u ^+ 2) = 'Re u ^+ 2 *+ 2 - `|u| ^+ 2.
  by rewrite normC2_Re_Im expr2 ReM -!expr2 mulr2n opprD addrA addrK.
have [Iu|Iu] := boolP (0 <= 'Im (z ^+ 2)).
  have uz : (z ^+ 2) ^+ n.+2 = x by rewrite -exprM.
  have := rootC_Re_max (isT : (0 < n.+2)%N) uz Iu.
  rewrite -/r -[r]sqrtCK -/y !ReIm zy lerD2r ler_pMn2r // => Rzy.
  rewrite (le_trans (real_ler_norm (Creal_Re z))) //.
  rewrite -(ler_pXn2r (isT : (0 < 2)%N)) ?nnegrE ?normr_ge0 //.
  by rewrite real_normK ?Creal_Re.
have : ~~ (0 <= 'Re z).
  apply: contra Iu => Rz.
  by rewrite expr2 ImM -mulr2n mulrn_wge0 ?mulr_ge0.
rewrite -real_ltNge ?Creal_Re ?real0 // => Rz.
exact: le_trans (ltW Rz) Ry.
Qed.

Lemma mulC_rect (a b c d : C) : (a + 'i * b) * (c + 'i * d) =
  (a * c - b * d) + 'i * (a * d + b * c).
Proof.
rewrite mulrDl !mulrDr -!addrA; congr (_ + _).
rewrite [RHS]addrC addrA; congr (_ + _).
  by rewrite mulrCA -mulrA.
by rewrite mulrACA -expr2 sqrCi mulN1r.
Qed.

Lemma sqrC_rect (a b : C) :
  (a + 'i * b) ^+ 2 = (a ^+ 2 - b ^+ 2) + 'i * (a * b *+ 2).
Proof. by rewrite expr2 mulC_rect -!expr2 [b * a]mulrC mulr2n. Qed.

Lemma cube_factor (z : C) : (z + 1) * (z ^+ 2 - z + 1) = z ^+ 3 + 1.
Proof.
rewrite mulrDl mul1r !mulrDr mulrN mulr1.
by rewrite -exprS -expr2 !addrA [_ - _ + z]addrAC subrK addrK.
Qed.

Lemma divCnK k (x : C) : (0 < k)%N -> x / k%:R *+ k = x.
Proof. by move=> k0; rewrite -mulr_natr divfK ?pnatr_eq0 -?lt0n. Qed.

Lemma sqrtC_char_mulrn k (w t : C) : (0 < k)%N ->
  t ^+ 2 = w *+ (k * k) -> 0 < 'Im t -> sqrtC w = t / k%:R.
Proof.
move=> k0 tw It; apply: sqrtC_char_Im.
  apply: (@pmulrnI _ (k * k)); first by rewrite muln_gt0 k0.
  by rewrite /= -[(k * k)%N]/(k ^ 2)%N -exprMn_n divCnK.
by move: It; rewrite -{1}(divCnK t k0) raddfMn /= pmulrn_lgt0.
Qed.

Lemma rootC_doubleK n (x : C) : (0 < n)%N ->
  (2 * n).-root x ^+ 2 = n.-root x.
Proof. by move=> n0; rewrite rootC_double // sqrtCK. Qed.

Lemma rootC_N1_inv n : (0 < n)%N ->
  (n.-root (-1 : C))^-1 = - n.-root (-1) ^+ n.-1.
Proof.
move=> n0; have w0 : n.-root (-1 : C) != 0.
  by rewrite rootC_eq0 // oppr_eq0 oner_eq0.
apply: (mulfI w0); rewrite mulfV // mulrN -exprS prednK // rootCK //.
by rewrite opprK.
Qed.

Lemma rect_div_gt0 k (a b : C) : (0 < k)%N -> 0 < a -> 0 < b ->
  0 < 'Re ((a + 'i * b) / k%:R) /\ 0 < 'Im ((a + 'i * b) / k%:R).
Proof.
move=> k0 a0 b0; have ra := gtr0_real a0; have rb := gtr0_real b0.
split; rewrite -(pmulrn_lgt0 _ k0) -raddfMn /= divCnK //.
  by rewrite Re_rect.
by rewrite Im_rect.
Qed.

Lemma ImM_gt0 (x y : C) : 0 < 'Re x -> 0 < 'Im x -> 0 < 'Re y ->
  0 < 'Im y -> 0 < 'Im (x * y).
Proof. by move=> *; rewrite ImM addr_gt0 ?mulr_gt0. Qed.

End RootChar.

Section Omega.

Variable C : numClosedFieldType.

Lemma omega1C : 1.-root (-1 : C) = -1.
Proof. exact: root1C. Qed.

Lemma omega2C : 2.-root (-1 : C) = 'i.
Proof. by rewrite imaginaryCE. Qed.

Lemma omega4C : 4.-root (-1 : C) = sqrtC 2 / 2 * (1 + 'i).
Proof.
rewrite (rootC_double _ (isT : (0 < 2)%N)) omega2C.
set s := sqrtC 2 / 2.
have -> : s * (1 + 'i) = s + 'i * s by rewrite mulrDr mulr1 mulrC.
have s0 : 0 < s by rewrite divr_gt0 ?sqrtC_gt0 ?ltr0n.
apply: sqrtC_char_Im; last by rewrite Im_rect ?ger0_real ?ltW.
rewrite sqrC_rect subrr add0r -expr2 expr_div_n sqrtCK expr2 invfM mulrA.
rewrite mulfV ?pnatr_eq0 // mul1r -mulr_natr mulVf ?pnatr_eq0 //.
by rewrite mulr1.
Qed.

Lemma omega3_val_sqr :
  ((1 + sqrtC 3 * 'i) / 2) ^+ 2 = (1 + sqrtC 3 * 'i) / 2 - 1 :> C.
Proof.
set y := (1 + _) / 2.
have ty : y *+ 2 = 1 + 'i * sqrtC 3.
  by rewrite /y -mulr_natr mulfVK ?pnatr_eq0 // [sqrtC 3 * _]mulrC.
have t2 : (y *+ 2) ^+ 2 = y *+ 2 *+ 2 - 4.
  rewrite ty sqrC_rect expr1n sqrtCK mul1r mulrnDl [RHS]addrAC.
  rewrite -mulrnAr; congr (_ + _).
  by apply/eqP; rewrite subr_eq addrAC eq_sym subr_eq -!natrD.
apply: (@pmulrnI _ 4) => //=.
by rewrite -[4%N]/(2 ^ 2)%N -exprMn_n t2 mulrnBl -mulrnA.
Qed.

Lemma omega3C : 3.-root (-1 : C) = (1 + sqrtC 3 * 'i) / 2.
Proof.
have y2 := omega3_val_sqr; set y := (1 + _) / 2 in y2 *.
have ty : y *+ 2 = 1 + 'i * sqrtC 3.
  by rewrite /y -mulr_natr mulfVK ?pnatr_eq0 // [sqrtC 3 * _]mulrC.
have Re1 : 'Re (1 : C) = 1 by apply/Creal_ReP; rewrite real1.
have Ry : 'Re y *+ 2 = 1.
  by rewrite -raddfMn /= ty Re_rect ?real1 ?ger0_real ?sqrtC_ge0 ?ler0n.
have Iy : 'Im y *+ 2 = sqrtC 3.
  by rewrite -raddfMn /= ty Im_rect ?real1 ?ger0_real ?sqrtC_ge0 ?ler0n.
have Ry0 : 0 <= 'Re y by rewrite -(pmulrn_lge0 _ (isT : (0 < 2)%N)) Ry ler01.
apply: rootC_char => //.
- by rewrite exprS y2 mulrBr mulr1 -expr2 y2 addrAC subrr add0r.
- by rewrite -(pmulrn_lge0 _ (isT : (0 < 2)%N)) Iy sqrtC_ge0 ler0n.
move=> z z3 Iz.
have : (z + 1) * (z ^+ 2 - z + 1) == 0 by rewrite cube_factor z3 addNr.
rewrite mulf_eq0 => /orP[|].
  rewrite addr_eq0 => /eqP ->; rewrite raddfN /= Re1.
  by rewrite (le_trans _ Ry0) // lerN10.
rewrite addr_eq0 subr_eq => /eqP z2.
have : (z - y) * (z + y) = (z - y) * 1.
  by rewrite -subr_sqr z2 y2 mulr1 opprB addrA [-1 + z]addrC subrK.
have [-> //|/eqP zy] := eqVneq z y.
have /mulfI zyI : z - y != 0 by rewrite subr_eq0; apply/eqP.
move=> /zyI /(congr1 (fun u => u - y)); rewrite addrK => ->.
by rewrite raddfB /= Re1 lerBlDr -mulr2n Ry.
Qed.

Lemma omega6C : 6.-root (-1 : C) = (sqrtC 3 + 'i) / 2.
Proof.
rewrite (rootC_double _ (isT : (0 < 3)%N)) omega3C.
have -> : sqrtC 3 + 'i = sqrtC 3 + 'i * 1 :> C by rewrite mulr1.
have r3 : sqrtC 3 \is @Num.real C by apply: ger0_real; rewrite sqrtC_ge0 ler0n.
apply: sqrtC_char_mulrn => //; last by rewrite Im_rect ?real1 ?ltr01.
rewrite mulnn mulrnA divCnK // sqrC_rect sqrtCK expr1n mulr1 mulrnDl.
rewrite [_ * 'i]mulrC -mulrnAr; congr (_ + _).
by apply/eqP; rewrite subr_eq natr1.
Qed.

Lemma omega12C : 12.-root (-1 : C) =
  ((sqrtC 6 + sqrtC 2) + (sqrtC 6 - sqrtC 2) * 'i) / 4.
Proof.
rewrite (rootC_double _ (isT : (0 < 6)%N)) omega6C.
set a := sqrtC 6 + _; set b := sqrtC 6 - _; rewrite [b * _]mulrC.
have r2 : sqrtC 2 \is @Num.real C by apply: ger0_real; rewrite sqrtC_ge0 ler0n.
have r6 : sqrtC 6 \is @Num.real C by apply: ger0_real; rewrite sqrtC_ge0 ler0n.
apply: sqrtC_char_mulrn => //; last first.
  rewrite /a /b Im_rect; [|exact: rpredD|exact: rpredB].
  by rewrite subr_gt0 ltr_rootC ?nnegrE ?ler0n // ltr_nat.
rewrite -[(4 * 4)%N]/(2 * 8)%N mulrnA divCnK // sqrC_rect subr_sqrDB.
have -> : a * b = 4.
  rewrite /a /b mulrC -subr_sqr !sqrtCK.
  by apply/eqP; rewrite subr_eq -natrD.
rewrite -[(6 : C)]/((2 * 3)%N%:R) natrM rootCMl ?ler0n //.
rewrite mulrAC -expr2 sqrtCK mulr_natl -mulrnA [RHS]mulrnDl.
by congr (_ + _); rewrite mulrnAr mulr_natr -mulrnA.
Qed.

Lemma omega3_sqrC : 3.-root (-1 : C) ^+ 2 = 3.-root (-1) - 1.
Proof. by rewrite omega3C omega3_val_sqr. Qed.

Lemma omega3_cycloC : 3.-root (-1 : C) ^+ 2 - 3.-root (-1) + 1 = 0.
Proof. by rewrite omega3_sqrC [_ - 1]addrC addrK addNr. Qed.

Lemma omega4_sqrC : 4.-root (-1 : C) ^+ 2 = 2.-root (-1).
Proof. exact: (rootC_doubleK _ (isT : (0 < 2)%N)). Qed.

Lemma omega6_sqrC : 6.-root (-1 : C) ^+ 2 = 3.-root (-1).
Proof. exact: (rootC_doubleK _ (isT : (0 < 3)%N)). Qed.

Lemma omega12_sqrC : 12.-root (-1 : C) ^+ 2 = 6.-root (-1).
Proof. exact: (rootC_doubleK _ (isT : (0 < 6)%N)). Qed.

Lemma omega4_cubeC : 4.-root (-1 : C) ^+ 3 = 4.-root (-1) * 'i.
Proof. by rewrite exprS omega4_sqrC omega2C. Qed.

(* paper eq. (2), second reading: omega_4 - omega_4 ^+ 3 = sqrt 2 *)
Lemma omega4_sqrt2C : 4.-root (-1 : C) - 4.-root (-1) ^+ 3 = sqrtC 2.
Proof.
rewrite omega4_cubeC -{1}[4.-root _]mulr1 -mulrBr omega4C -mulrA.
rewrite -!mulrA [(1 + _) * _]mulrC -subr_sqr sqrCi expr1n opprK.
by rewrite mulVf ?mulr1 // pnatr_eq0.
Qed.

Lemma omega4_invC : 4.-root (-1 : C) + (4.-root (-1))^-1 = sqrtC 2.
Proof. by rewrite rootC_N1_inv // omega4_sqrt2C. Qed.

Lemma omega6_cubeC : 6.-root (-1 : C) ^+ 3 = 'i.
Proof.
rewrite -omega2C; symmetry; apply: sqrtC_char_Im.
  by rewrite -exprM rootCK.
rewrite exprS omega6_sqrC omega6C omega3C.
have s3 : 0 < sqrtC 3 :> C by rewrite sqrtC_gt0 ltr0n.
have -> : sqrtC 3 + 'i = sqrtC 3 + 'i * 1 :> C by rewrite mulr1.
rewrite [sqrtC 3 * _]mulrC.
have [R1 I1] := rect_div_gt0 (isT : (0 < 2)%N) s3 ltr01.
have [R2 I2] := rect_div_gt0 (isT : (0 < 2)%N) ltr01 s3.
by rewrite ImM_gt0.
Qed.

Lemma omega12_cubeC : 12.-root (-1 : C) ^+ 3 = 4.-root (-1).
Proof.
rewrite (rootC_double _ (isT : (0 < 2)%N)); symmetry.
apply: sqrtC_char_Im.
  by rewrite -exprM mulnC exprM omega12_sqrC omega6_cubeC omega2C.
rewrite exprS omega12_sqrC omega12C omega6C.
have s3 : 0 < sqrtC 3 :> C by rewrite sqrtC_gt0 ltr0n.
have a0 : 0 < sqrtC 6 + sqrtC 2 :> C.
  by rewrite addr_gt0 ?sqrtC_gt0 ?ltr0n.
have b0 : 0 < sqrtC 6 - sqrtC 2 :> C.
  by rewrite subr_gt0 ltr_rootC ?nnegrE ?ler0n // ltr_nat.
have -> : sqrtC 3 + 'i = sqrtC 3 + 'i * 1 :> C by rewrite mulr1.
rewrite [_ * 'i]mulrC.
have [R1 I1] := rect_div_gt0 (isT : (0 < 4)%N) a0 b0.
have [R2 I2] := rect_div_gt0 (isT : (0 < 2)%N) s3 ltr01.
by rewrite ImM_gt0.
Qed.

End Omega.

Section SmallRootC.

Variable C : numClosedFieldType.

Lemma rootC_smallroot : smallroot (rootC_negroot C).
Proof.
split; rewrite /= omega2C.
- exact: omega3C.
- exact: omega4C.
- exact: omega6C.
- exact: omega12C.
Qed.

End SmallRootC.
