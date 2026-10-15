(******************************************************************************)
(* Tutorial 35: a trigonometric identity through C and radcan.               *)
(* IMO 1963, problem 5: cos(pi/7) - cos(2pi/7) + cos(3pi/7) = 1/2, on the    *)
(* reals of the Rocq standard library.  We go to C = R[i] (mathcomp          *)
(* real-closed), where z = cos(pi/7) + i sin(pi/7) satisfies z^7 = -1 and    *)
(* z <> -1, hence Phi_14(z) = 0; the identity is then pure algebra in z,     *)
(* proved by radcan_sym, and we come back to R by taking real parts.         *)
(* Second part: z is mathcomp's principal root 7.-root (-1) (z_root), by    *)
(* the facts of UnitArc.v (primitivity, largest real part); then plain       *)
(* radcan proves the identity on 7.-root (-1) (imo1963_omega).               *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.real_closed Require Import complex.
From Radcan Require Import Rstruct PosRoot Syntax Radcan Tactic Sym SymTac.
From Radcan Require Import UnitArc.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope complex_scope.

(* the complex exponential e^(ix), without exp *)
Definition E (x : R) : R[i] := cos x +i* sin x.

Lemma EE x : E x = (cos x)%:C + 'i * (sin x)%:C.
Proof. by rewrite [LHS]complexE. Qed.

Lemma i2 : ('i%C : R[i]) ^+ 2 = -1.
Proof. exact: sqr_i. Qed.

(* the complex product, with i as a symbol such that i^2 = -1 *)
Lemma cmul_gen (K : numFieldType) (i a b c d : K) : i ^+ 2 = -1 ->
  (a + i * b) * (c + i * d) = (a * c - b * d) + i * (b * c + a * d).
Proof. move=> hi. radcan_sym. Qed.

Lemma EM x y : E x * E y = E (x + y).
Proof.
rewrite !EE cos_plus sin_plus (@cmul_gen _ _ _ _ _ _ i2).
by rewrite -!rmorphM -rmorphB -rmorphD.
Qed.

(* de Moivre *)
Lemma EX x n : E x ^+ n = E (INR n * x).
Proof.
elim: n => [|n IH]; first by rewrite expr0 Rmult_0_l /E cos_0 sin_0.
by rewrite exprSr IH EM S_INR; congr E; ring.
Qed.

Lemma EN x : E x * E (- x) = 1.
Proof. by rewrite EM Rplus_opp_r /E cos_0 sin_0. Qed.

Lemma ENE x : E x + E (- x) = (2 * cos x)%:C.
Proof.
rewrite !EE cos_neg sin_neg (@rmorphN _ _ (real_complex R)).
rewrite mulrN addrACA subrr addr0 -rmorphD.
by rewrite mulr_natl mulr2n.
Qed.

Definition t : R := Rdiv PI (IZR 7).
Definition z := E t.

Lemma z7 : z ^+ 7 = -1.
Proof.
rewrite /z EX EE.
have -> : Rmult (INR 7) t = PI by rewrite /t /=; field.
by rewrite cos_PI sin_PI rmorph0 mulr0 addr0 rmorphN1.
Qed.

Lemma Ezk k : E (Rmult (INR k) t) = z ^+ k.
Proof. by rewrite /z EX. Qed.

(* e^(-ikt) = - z^(7-k), since z^7 = -1 *)
Lemma Enk k : (k <= 7)%N -> E (Ropp (Rmult (INR k) t)) = - z ^+ (7 - k).
Proof.
move=> hk.
have h1 : z ^+ k * E (Ropp (Rmult (INR k) t)) = 1 by rewrite -Ezk EN.
have h2 : z ^+ (7 - k) * z ^+ k = -1 by rewrite -exprD subnK // z7.
by rewrite -[RHS]mulr1 -h1 mulNr mulrA h2 mulN1r opprK.
Qed.

(* z is a root of Phi_14 = (X^7 + 1) / (X + 1) *)
Lemma Phi14 : z ^+ 6 = z ^+ 5 - z ^+ 4 + z ^+ 3 - z ^+ 2 + z - 1.
Proof.
have zN1 : z + 1 != 0.
  apply/eqP => /(congr1 (@complex.Im R)) /=.
  rewrite /= addr0; have := sin_gt_0 t.
  move=> h hs.
  have tpos : Rlt 0 t by rewrite /t; have := PI_RGT_0; lra.
  have tlt : Rlt t PI by rewrite /t; have := PI_RGT_0; lra.
  by have := h tpos tlt; rewrite hs; exact: Rlt_irrefl.
have e : (z + 1) * (z ^+ 6 - z ^+ 5 + z ^+ 4 - z ^+ 3 + z ^+ 2 - z + 1) = 0.
  by have h7 := z7; move: z h7 => w h7; radcan_sym.
move/eqP: e; rewrite mulf_eq0 (negbTE zN1) /= => /eqP hp.
apply/eqP; rewrite -subr_eq0 -[X in _ == X]hp; apply/eqP.
by move: z hp => w _; radcan.
Qed.

(* the identity in C: 2 cos(kt) = z^k + z^-k, then algebra modulo Phi_14 *)
Lemma mainC :
  (E (Rmult (INR 1) t) + E (Ropp (Rmult (INR 1) t)))
  - (E (Rmult (INR 2) t) + E (Ropp (Rmult (INR 2) t)))
  + (E (Rmult (INR 3) t) + E (Ropp (Rmult (INR 3) t))) = 1.
Proof.
rewrite !Ezk !Enk //=.
have h6 := Phi14; move: z h6 => w h6.
radcan_sym.
Qed.

(* back to R: real parts *)
Lemma cos_pi7_mc :
  2 * cos (Rmult (INR 1) t) - 2 * cos (Rmult (INR 2) t)
  + 2 * cos (Rmult (INR 3) t) = 1.
Proof.
have := mainC; rewrite !ENE -!rmorphB -rmorphD.
by move=> /(congr1 (@complex.Re R)).
Qed.

(* Second part: z is the principal root 7.-root (-1) of mathcomp *)

Lemma ImE x : 'Im (E x) = (sin x)%:C.
Proof. by rewrite -complexIm. Qed.

Lemma ReE x : 'Re (E x) = (cos x)%:C.
Proof. by rewrite -complexRe. Qed.

Lemma tpos : Rlt 0 t.
Proof. by rewrite /t; have := PI_RGT_0; lra. Qed.

Lemma z14 : z ^+ 14 = 1.
Proof. by rewrite -[14%N]/(7 * 2)%N exprM z7 sqrrN expr1n. Qed.

Lemma z2N1 : z ^+ 2 != 1.
Proof.
rewrite /z EX; apply/eqP => /(congr1 (@complex.Im R)) /= h.
have : Rlt 0 (sin (INR 2 * t)).
  apply: sin_gt_0; first by have := tpos; rewrite /=; lra.
  by rewrite /t /=; have := PI_RGT_0; lra.
by rewrite h; exact: Rlt_irrefl.
Qed.

(* z is a primitive 14th root of unity: its order divides 14, and
   z ^+ 2 <> 1, z ^+ 7 = -1 <> 1 *)
Lemma zprim : 14.-primitive_root z.
Proof.
have [m mp m14] := prim_order_exists (isT : (0 < 14)%N) z14.
have : m \in divisors 14 by rewrite -dvdn_divisors.
have zm := prim_expr_order mp.
rewrite (_ : divisors 14 = [:: 1; 2; 7; 14]%N) //.
rewrite !inE => /or4P[] /eqP me; rewrite me in mp zm *; rewrite //.
- by move: z2N1; rewrite expr2 -[z]expr1 zm mul1r eqxx.
- by move: z2N1; rewrite zm eqxx.
- by move: (@N1_neq1 R[i]); rewrite -z7 zm eqxx.
Qed.

(* w = 7.-root (-1) is a power z ^+ j; 'Im w >= 0 gives j <= 7, and w has
   the largest real part (rootC_N1_max), so j = 1 *)
Lemma z_root : z = 7.-root (-1 : R[i]).
Proof.
set w := 7.-root (-1 : R[i]).
have wp : 14.-primitive_root w by exact: (@rootC_N1_prim R[i] 7 isT).
have w14 : w ^+ 14 = 1 := prim_expr_order wp.
have [[j jlt] /= wj] := prim_rootP zprim w14.
have wE : w = E (INR j * t) by rewrite wj /z EX.
have Iw := Im_rootC_N1_ge0 R[i] 7; rewrite -/w wE ImE in Iw.
have {Iw} /RleP Iw : 0 <= sin (INR j * t).
  by rewrite -(lecR (R := R)) rmorph0.
have Iz : 0 <= 'Im z.
  rewrite ImE -(rmorph0 (real_complex R)) lecR; apply/RleP/Rlt_le.
  by apply: sin_gt_0; [exact: tpos | rewrite /t; have := PI_RGT_0; lra].
have z1 : z != 1 by apply: contraNneq z2N1 => ->; rewrite expr1n.
have Rw := @rootC_N1_max R[i] 7 z isT z14 Iz z1.
rewrite -/w wE !ReE lecR in Rw; move/RleP: Rw => Rw.
have tp := tpos.
have tPI : Rmult 7 t = PI by rewrite /t; field.
case: (ltngtP j 1) => [j0|j1|j1]; last by rewrite wE j1 /= Rmult_1_l.
- (* j = 0: w = 1, but w ^+ 7 = -1 *)
  have j0' : j = 0%N by case: j j0 {jlt wj wE Iw Rw}.
  have w1 : w = 1 by rewrite wj j0' expr0.
  have := @rootCK R[i] 7 isT (-1); rewrite -/w w1 expr1n => h.
  by move: (@N1_neq1 R[i]); rewrite -h eqxx.
- have j2 : Rle 2 (INR j).
    by have := le_INR 2 j (ssrnat.leP j1); rewrite /=; lra.
  have j13 : Rle (INR j) 13.
    by have := le_INR j 13 (ssrnat.leP (jlt : (j <= 13)%N)); rewrite /=; lra.
  case: (leqP j 7) => j7.
  + (* 2 <= j <= 7: cos is decreasing on [0, PI] *)
    have j7' : Rle (INR j) 7.
      by have := le_INR j 7 (ssrnat.leP j7); rewrite /=; lra.
    have h0 : Rle (2 * t) (INR j * t) by apply: Rmult_le_compat_r; lra.
    have h1 : Rle (INR j * t) (7 * t) by apply: Rmult_le_compat_r; lra.
    have ht : Rle t PI by lra.
    have hj0 : Rle 0 (INR j * t) by lra.
    have hjP : Rle (INR j * t) PI by lra.
    have hlt : Rlt t (INR j * t) by lra.
    have hc := cos_decreasing_1 _ _ (Rlt_le _ _ tp) ht hj0 hjP hlt.
    by exfalso; apply: (Rlt_not_le _ _ hc); exact: Rw.
  + (* 8 <= j <= 13: sin is negative on ]PI, 2 PI[ *)
    have j8 : Rle 8 (INR j).
      by have := le_INR 8 j (ssrnat.leP j7); rewrite /=; lra.
    have h0 : Rle (8 * t) (INR j * t) by apply: Rmult_le_compat_r; lra.
    have h1 : Rle (INR j * t) (13 * t) by apply: Rmult_le_compat_r; lra.
    have hl : Rlt PI (INR j * t) by lra.
    have hr : Rlt (INR j * t) (2 * PI) by lra.
    by exfalso; apply: (Rlt_not_le _ _ (sin_lt_0 _ hl hr)); exact: Iw.
Qed.

(* the identity in C again, now by plain radcan on 7.-root (-1): the
   cyclotomic reduction of Tutorial 34 knows Phi_14 *)
Lemma mainC_omega :
  (E (Rmult (INR 1) t) + E (Ropp (Rmult (INR 1) t)))
  - (E (Rmult (INR 2) t) + E (Ropp (Rmult (INR 2) t)))
  + (E (Rmult (INR 3) t) + E (Ropp (Rmult (INR 3) t))) = 1.
Proof. rewrite !Ezk !Enk //= z_root. radcan. Qed.

Local Open Scope R_scope.

Theorem imo1963 : cos (PI / 7) - cos (2 * PI / 7) + cos (3 * PI / 7) = 1 / 2.
Proof.
have h : Rplus (Rminus (Rmult 2 (cos (Rmult (INR 1) t)))
                       (Rmult 2 (cos (Rmult (INR 2) t))))
               (Rmult 2 (cos (Rmult (INR 3) t))) = 1 := cos_pi7_mc.
move: h; rewrite /t /=.
have -> : 1 * (PI / 7) = PI / 7 by field.
have -> : (1 + 1) * (PI / 7) = 2 * PI / 7 by field.
have -> : (1 + 1 + 1) * (PI / 7) = 3 * PI / 7 by field.
lra.
Qed.

(* the same theorem through mainC_omega *)
Theorem imo1963_omega :
  cos (PI / 7) - cos (2 * PI / 7) + cos (3 * PI / 7) = 1 / 2.
Proof.
have h : Rplus (Rminus (Rmult 2 (cos (Rmult (INR 1) t)))
                       (Rmult 2 (cos (Rmult (INR 2) t))))
               (Rmult 2 (cos (Rmult (INR 3) t))) = 1.
  have := mainC_omega; rewrite !ENE -!rmorphB -rmorphD.
  by move=> /(congr1 (@complex.Re R)).
move: h; rewrite /t /=.
have -> : 1 * (PI / 7) = PI / 7 by field.
have -> : (1 + 1) * (PI / 7) = 2 * PI / 7 by field.
have -> : (1 + 1 + 1) * (PI / 7) = 3 * PI / 7 by field.
lra.
Qed.
