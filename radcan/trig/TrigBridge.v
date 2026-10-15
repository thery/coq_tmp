(******************************************************************************)
(* TrigBridge: the mathematical bridge from Stdlib trigonometry to radcan.   *)
(* C = R[i] (mathcomp real-closed complex) over the Stdlib reals R, made an  *)
(* rcfType by Rstruct.  E x := cos x +i* sin x  (= e^(ix), without exp).     *)
(*                                                                            *)
(*   EE, ReE, ImE, E0, EM (E x * E y = E (x + y)), EN, E_neq0, EV, EX (de     *)
(*   Moivre), EZ (integer multiples, through zpowC: w ^+ p or (w ^+ p)^-1)   *)
(*   ENE, ESE : E x +- E (- x) = (2 cos x)%:C, 'i * (2 sin x)%:C             *)
(*   cos_E, sin_E, tan_E : cos, sin, tan as rational functions of E x        *)
(*                (tan with Stdlib's x / 0 = 0, matching mathcomp's)         *)
(*   E_neq1, E_prim : E (PI / n) is a primitive (2 n)-th root of unity       *)
(*   E_root   : E (PI / n) = n.-root (-1)     for every n > 0                *)
(*   E_rat, E_ratn, E_rootZ, E_ratZ : E (k PI / n) as powers of n.-root (-1) *)
(*   realC_inj, realC_eq, realC_add .. realC_IZR : moving %:C through the    *)
(*                Stdlib operations, and back to R                           *)
(* Scopes: arguments of E and of %:C are Stdlib R terms (R_scope), the rest  *)
(* is ring_scope on C.  Both scopes have key %R: write Rplus, Rmult, ...     *)
(* when an R term must be explicit.                                          *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.real_closed Require Import complex.
From Radcan Require Import Rstruct RootRstd OmegaC UnitArc.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope complex_scope.

(* the complex exponential e^(ix), without exp *)
Definition E (x : R) : R[i] := cos x +i* sin x.

Lemma EE x : E x = (cos x)%:C + 'i * (sin x)%:C.
Proof. by rewrite [LHS]complexE. Qed.

Lemma ReE x : complex.Re (E x) = cos x. Proof. by []. Qed.
Lemma ImE x : complex.Im (E x) = sin x. Proof. by []. Qed.

Lemma E0 : E 0 = 1.
Proof. by rewrite /E cos_0 sin_0. Qed.

Lemma EM x y : E x * E y = E (x + y).
Proof.
apply/eqP; rewrite eq_complex /= cos_plus sin_plus.
by rewrite eqxx /= addrC.
Qed.

Lemma EN x : E x * E (- x) = 1.
Proof. by rewrite EM Rplus_opp_r E0. Qed.

Lemma E_neq0 x : E x != 0.
Proof.
apply/eqP => h; move: (EN x); rewrite h mul0r => /eqP.
by rewrite eq_sym oner_eq0.
Qed.

Lemma EV x : (E x)^-1 = E (- x).
Proof. by apply: (mulfI (E_neq0 x)); rewrite EN divff ?E_neq0. Qed.

(* de Moivre *)
Lemma EX x n : E x ^+ n = E (INR n * x).
Proof.
elim: n => [|n IH]; first by rewrite expr0 /= Rmult_0_l E0.
by rewrite exprSr IH EM S_INR Rmult_plus_distr_r Rmult_1_l.
Qed.

(* integer powers: x ^+ p for k = p > 0, (x ^+ p)^-1 for k = - p < 0 *)
Definition zpowC (w : R[i]) (k : Z) : R[i] :=
  match k with
  | Z0 => 1
  | Zpos p => w ^+ Pos.to_nat p
  | Zneg p => (w ^+ Pos.to_nat p)^-1
  end.

Lemma EZ x k : E (IZR k * x) = zpowC (E x) k.
Proof.
case: k => [|p|p] /=; first by rewrite Rmult_0_l E0.
  by rewrite EX INR_IPR.
by rewrite EX EV INR_IPR Ropp_mult_distr_l.
Qed.

Lemma ENE x : E x + E (- x) = (Rmult 2 (cos x))%:C.
Proof.
apply/eqP; rewrite eq_complex /= cos_neg sin_neg subrr eqxx andbT.
by rewrite -RplusE; apply/eqP; lra.
Qed.

Lemma ESE x : E x - E (- x) = 'i * (Rmult 2 (sin x))%:C.
Proof.
apply/eqP; rewrite eq_complex /= cos_neg sin_neg.
rewrite subrr !mul0r mulr0 subr0 eqxx /= add0r mul1r -RminusE.
by apply/eqP; lra.
Qed.

Lemma IZR2 : IZR 2 = 2%:R :> R. Proof. by []. Qed.

Lemma cos_E x : (cos x)%:C = (E x + (E x)^-1) / 2.
Proof.
rewrite EV ENE RmultE IZR2 rmorphM /= rmorph_nat.
by rewrite [2 * _]mulrC mulfK // pnatr_eq0.
Qed.

Lemma sin_E x : (sin x)%:C = (E x - (E x)^-1) / (2 * 'i).
Proof.
rewrite EV ESE RmultE IZR2 rmorphM /= rmorph_nat.
have hi : (2 * 'i : R[i]) != 0 by rewrite mulf_neq0 ?pnatr_eq0 ?neq0Ci.
by rewrite mulrA ['i * 2]mulrC mulrAC divff // mul1r.
Qed.

(* Stdlib: tan x = sin x / cos x, and x / 0 = 0 on both sides *)
Lemma tan_E x :
  (tan x)%:C = (E x - (E x)^-1) / ('i * (E x + (E x)^-1)).
Proof.
rewrite /tan RdivE rmorphM /= fmorphV /= sin_E cos_E.
set a := (E x - _); set b := (E x + _).
have h2 : (2 : R[i]) != 0 by rewrite pnatr_eq0.
rewrite invf_div !invfM -!mulrA; congr (a * _).
by rewrite mulrCA [2^-1 * _]mulrA mulVf // mul1r.
Qed.

(* E x = 1 has no solution in ]0, 2 PI[ *)
Lemma E_neq1 x : Rlt 0 x -> Rlt x (2 * PI) -> E x != 1.
Proof.
move=> x0 x2; apply/eqP => /eqP; rewrite eq_complex /=.
move=> /andP[/eqP c1 /eqP s0].
have [xP|[xP|xP]] := Rtotal_order x PI.
- by have := sin_gt_0 _ x0 xP; rewrite s0 => /Rlt_irrefl.
- by move: c1; rewrite xP cos_PI => h; have : IZR (-1) = R1 := h; lra.
by have := sin_lt_0 _ xP x2; rewrite s0 => /Rlt_irrefl.
Qed.

Lemma INR_pos n : (0 < n)%N -> Rlt 0 (INR n).
Proof. by move=> n0; apply: lt_0_INR; apply/ssrnat.ltP. Qed.

Lemma INR_lt m n : (m < n)%N -> Rlt (INR m) (INR n).
Proof. by move=> mn; apply: lt_INR; apply/ssrnat.ltP. Qed.

Lemma INR_le m n : (m <= n)%N -> Rle (INR m) (INR n).
Proof. by move=> mn; apply: le_INR; apply/ssrnat.leP. Qed.

(* j * (PI / n) lies in ]0, 2 PI[ for 0 < j < 2 n *)
Lemma arc_in n j : (0 < j)%N -> (j < 2 * n)%N ->
  Rlt 0 (INR j * (PI / INR n)) /\ Rlt (INR j * (PI / INR n)) (2 * PI).
Proof.
move=> j0 jn; have n0 : (0 < n)%N by case: n jn => //; rewrite muln0.
have hn := INR_pos _ n0; have hj := INR_pos _ j0.
have h2 : Rlt (INR j) (2 * INR n).
  by have := INR_lt _ _ jn; rewrite mult_INR /=; lra.
have e : Rmult (INR j * (PI / INR n)) (INR n) = Rmult (INR j) PI.
  by field; lra.
have pi := PI_RGT_0.
split; apply: (Rmult_lt_reg_r (INR n)) => //; rewrite e; nra.
Qed.

(* E (PI / n) has order exactly 2 n: E (j PI / n) <> 1 for 0 < j < 2 n *)
Lemma E_prim n : (0 < n)%N -> (2 * n).-primitive_root (E (PI / INR n)).
Proof.
move=> n0; set t := Rdiv PI (INR n).
have hn := INR_pos _ n0.
have m0 : (0 < 2 * n)%N by rewrite muln_gt0.
have e2 : E t ^+ (2 * n) = 1.
  rewrite EX mult_INR /=.
  have -> : Rmult (Rmult (Rplus 1 1) (INR n)) t = Rmult 2 PI.
    by rewrite /t; field; lra.
  by apply/eqP; rewrite eq_complex /= cos_2PI sin_2PI !eqxx.
have [m mp m2] := prim_order_exists m0 e2.
suff -> : (2 * n)%N = m by [].
apply/eqP; rewrite eq_sym eqn_leq dvdn_leq //=.
have m0' := prim_order_gt0 mp.
rewrite leqNgt; apply/negP => mlt.
have [a b] := arc_in n m m0' mlt.
by move: (E_neq1 _ a b); rewrite -EX (prim_expr_order mp) eqxx.
Qed.

Lemma E_PI : E PI = -1.
Proof.
apply/eqP; rewrite eq_complex /= cos_PI sin_PI.
by rewrite oppr0 !eqxx.
Qed.

(* E (PI / n) is mathcomp's principal root n.-root (-1), for every n > 0:
   by rootC_char, the n-th roots of -1 are the E (j PI / n), j < 2 n
   (E_prim); those with 0 <= 'Im have 1 <= j <= n (sin < 0 on
   ]PI, 2 PI[, j = 0 gives 1 <> -1), and cos is decreasing on [0, PI] *)
Lemma E_root n : (0 < n)%N -> E (PI / INR n) = n.-root (-1 : R[i]).
Proof.
move=> n0; set t := Rdiv PI (INR n).
have hn := INR_pos _ n0; have pi := PI_RGT_0.
have tn : E t ^+ n = -1.
  by rewrite EX -E_PI; congr E; rewrite /t; field; lra.
have t0 : Rlt 0 t by apply: Rdiv_lt_0_compat.
have tP : Rle t PI.
  have n1 : Rle 1 (INR n) by have := INR_le _ _ n0.
  rewrite /t; apply: (Rmult_le_reg_r (INR n)) => //.
  by field_simplify; nra.
have ReC x : 'Re (E x) = (cos x)%:C by rewrite -complexRe.
have ImC x : 'Im (E x) = (sin x)%:C by rewrite -complexIm.
symmetry; apply: rootC_char => //.
  rewrite ImC -(rmorph0 (real_complex R)) lecR.
  by apply/RleP; apply: sin_ge_0; lra.
move=> z zn Iz.
have tp := E_prim _ n0.
have z2 : z ^+ (2 * n) = 1 by rewrite mulnC exprM zn sqrrN expr1n.
have [[j jlt] /= zj] := prim_rootP tp z2.
rewrite zj EX in Iz zn *.
rewrite ImC -(rmorph0 (real_complex R)) lecR in Iz; move/RleP: Iz => Iz.
rewrite !ReC lecR; apply/RleP; rewrite -/t in Iz zn *.
case: (posnP j) => [j0|j0].
  move: zn; rewrite j0 /= Rmult_0_l E0 expr1n => /eqP.
  by rewrite -subr_eq0 opprK (_ : 1 + 1 = 2%:R) // pnatr_eq0.
case: (leqP j n) => jn; last first.
  have [a b] := arc_in n j j0 jlt.
  have jP : Rlt PI (INR j * t).
    have hj := INR_lt _ _ jn.
    rewrite /t; apply: (Rmult_lt_reg_r (INR n)) => //.
    by field_simplify; nra.
  by have := sin_lt_0 _ jP b => /Rlt_not_le.
have hj1 : Rle 1 (INR j) by have := INR_le _ _ j0.
have hjn : Rle (INR j) (INR n) := INR_le _ _ jn.
have jP : Rle (INR j * t) PI.
  rewrite /t; apply: (Rmult_le_reg_r (INR n)) => //.
  by field_simplify; nra.
have [j1|j1] := Rle_lt_or_eq_dec _ _ hj1; last first.
  by rewrite -j1 Rmult_1_l; apply: Rle_refl.
by apply: Rlt_le; apply: cos_decreasing_1; nra.
Qed.

(* rational multiples of PI: integer powers of the principal root *)
Lemma E_rat k n : (0 < n)%N ->
  E (IZR k * PI / INR n) = zpowC (n.-root (-1 : R[i])) k.
Proof.
move=> n0; rewrite -E_root // -EZ; congr E.
by rewrite /Rdiv Rmult_assoc.
Qed.

Lemma E_ratn k n : (0 < n)%N ->
  E (INR k * PI / INR n) = n.-root (-1 : R[i]) ^+ k.
Proof.
move=> n0; rewrite -E_root // EX; congr E.
by rewrite /Rdiv Rmult_assoc.
Qed.

Lemma Pos_to_nat_gt0 p : (0 < Pos.to_nat p)%N.
Proof. by apply/ssrnat.ltP; apply: Pos2Nat.is_pos. Qed.

Lemma IZR_posINR p : IZR (Zpos p) = INR (Pos.to_nat p).
Proof. by rewrite INR_IPR. Qed.

(* the same with a numeral denominator, as in PI / 7 or 2 * PI / 7 *)
Lemma E_rootZ p :
  E (PI / IZR (Zpos p)) = (Pos.to_nat p).-root (-1 : R[i]).
Proof. by rewrite IZR_posINR E_root // Pos_to_nat_gt0. Qed.

Lemma E_ratZ k p : E (IZR k * PI / IZR (Zpos p)) =
  zpowC ((Pos.to_nat p).-root (-1 : R[i])) k.
Proof. by rewrite IZR_posINR E_rat // Pos_to_nat_gt0. Qed.

(* back to R *)
Lemma realC_inj (a b : R) : a%:C = b%:C -> a = b.
Proof. by move=> /(congr1 (@complex.Re R)). Qed.

Lemma realC_eq (a b : R) : a%:C = b%:C -> a = b.
Proof. exact: realC_inj. Qed.

Lemma realC_add (a b : R) : (Rplus a b)%:C = a%:C + b%:C.
Proof. exact: rmorphD. Qed.

Lemma realC_sub (a b : R) : (Rminus a b)%:C = a%:C - b%:C.
Proof. exact: rmorphB. Qed.

Lemma realC_opp (a : R) : (Ropp a)%:C = - a%:C.
Proof. exact: rmorphN. Qed.

Lemma realC_mul (a b : R) : (Rmult a b)%:C = a%:C * b%:C.
Proof. exact: rmorphM. Qed.

Lemma realC_inv (a : R) : (Rinv a)%:C = (a%:C)^-1.
Proof. exact: fmorphV. Qed.

Lemma realC_div (a b : R) : (Rdiv a b)%:C = a%:C / b%:C.
Proof. exact: fmorph_div. Qed.

Lemma realC_pow (a : R) n : (pow a n)%:C = a%:C ^+ n.
Proof. by rewrite RpowE rmorphXn. Qed.

Lemma realC_INR n : (INR n)%:C = n%:R :> R[i].
Proof. by rewrite INRE rmorph_nat. Qed.

Lemma realC_IZR k : (IZR k)%:C =
  match k with Z0 => 0 | Zpos p => (Pos.to_nat p)%:R
  | Zneg p => - (Pos.to_nat p)%:R end :> R[i].
Proof.
case: k => [|p|p] /=; first exact: rmorph0.
  by rewrite -realC_INR INR_IPR.
by rewrite -realC_INR INR_IPR -rmorphN.
Qed.

Lemma realC_0 : R0%:C = 0 :> R[i]. Proof. exact: rmorph0. Qed.
Lemma realC_1 : R1%:C = 1 :> R[i]. Proof. exact: rmorph1. Qed.

(* non-vacuity: E (PI / 2) is the imaginary unit *)
Example E_PI2 : E (PI / 2) = 'i.
Proof. by rewrite E_rootZ omega2C. Qed.
