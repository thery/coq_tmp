(******************************************************************************)
(* Principal roots of -1 and composition of principal roots on a              *)
(* numClosedFieldType, proved without trigonometry.  For n > 0,               *)
(* n.-root (-1) is the nth root of -1 with minimal nonnegative argument, i.e. *)
(* "e^(i pi / n)"; this file shows that it is a primitive 2nth root of unity  *)
(* (as announced in the header of algC.v) and that principal roots compose:   *)
(*      eq_rootC_Re_max == n.-root x is the nth root of x with nonnegative    *)
(*                         imaginary part and maximal real part               *)
(*         rootCN1_prim == (2 * n).-primitive_root (n.-root (-1))  (0 < n)    *)
(*       rootCN1_Re_max == n.-root (-1) has maximal real part among the 2nth  *)
(*                         roots of unity w != 1 with 0 <= 'Im w              *)
(*        rootCN1_index == (n * k).-root (-1) ^+ k = n.-root (-1)             *)
(*             rootC_mul == (n * k).-root x = n.-root (k.-root x), for all x  *)
(*         exp_rootC_mul == (n * k).-root x ^+ n = k.-root x       (0 < n)    *)
(* The proofs use an elementary calculus of arguments on the closed upper     *)
(* half of the unit circle, where u comes before v when 'Re v <= 'Re u.       *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import div choice fintype tuple finfun bigop prime order.
From mathcomp Require Import ssralg poly finset fingroup finalg zmodp cyclic.
From mathcomp Require Import ssrnum ssrint archimedean polydiv separable.
From mathcomp Require Import cyclotomic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section NthRootUnity.

Variable C : numClosedFieldType.
Implicit Types (p q t w z a b A B : C).

Lemma eq_rootC_Re_max n (x y : C) : (0 < n)%N -> y ^+ n = x -> 0 <= 'Im y ->
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



Local Lemma arc_Im p q : `|p| = `|q| -> 0 <= 'Im p -> 0 <= 'Im q ->
  'Re q <= 'Re p -> 0 <= 'Im (q * p^*).
Proof.
move=> npq; rewrite ImM Re_conj Im_conj mulrN addrC subr_ge0.
have := congr1 (fun z => z ^+ 2) npq; rewrite /= !normC2_Re_Im.
have ra := Creal_Re p; have rb := Creal_Im p.
have rc := Creal_Re q; have rd := Creal_Im q.
move: ra rb rc rd; set a := 'Re p; set b := 'Im p.
set c := 'Re q; set d := 'Im q => ra rb rc rd E b0 d0 ca.
have sq (x y u v : C) : x ^+ 2 + y ^+ 2 = u ^+ 2 + v ^+ 2 ->
    (u ^+ 2 <= x ^+ 2) = (y ^+ 2 <= v ^+ 2).
  by move=> e; rewrite -(lerD2l (x ^+ 2) (y ^+ 2)) e lerD2r.
have r0 : (0 : C) \is Num.real by [].
have /orP[c0|c0] := real_leVge r0 rc.
  have a0 : 0 <= a := le_trans c0 ca.
  have bd : b <= d.
    by rewrite -ler_sqr ?nnegrE // -(sq _ _ _ _ E) ler_sqr ?nnegrE.
  exact: le_trans (ler_wpM2l c0 bd) (ler_wpM2r d0 ca).
have /orP[a0|a0] := real_leVge r0 ra.
  by rewrite (le_trans (_ : _ <= 0)) ?mulr_ge0 // mulr_le0_ge0.
have db : d <= b.
  rewrite -ler_sqr ?nnegrE // -(sq c d a b) //.
  rewrite -[a ^+ 2]sqrrN -[c ^+ 2]sqrrN ler_sqr ?nnegrE ?oppr_ge0 //.
  by rewrite lerN2.
exact: le_trans (ler_wpM2r b0 ca) (ler_wnM2l a0 db).
Qed.

Local Lemma arc_lt p q : `|p| = `|q| -> 0 <= 'Im p -> 0 <= 'Im q ->
  0 < 'Im (q * p^*) -> 'Re q < 'Re p.
Proof.
move=> npq Ip Iq Iqp; rewrite real_ltNge ?Creal_Re //; apply/negP => pq.
have := arc_Im (esym npq) Iq Ip pq.
have -> : p * q^* = (q * p^*)^* by rewrite rmorphM /= conjCK mulrC.
rewrite Im_conj oppr_ge0 => h.
by have := lt_le_trans Iqp h; rewrite ltxx.
Qed.

Local Lemma unity_norm m w : (0 < m)%N -> w ^+ m = 1 -> `|w| = 1.
Proof.
move=> m0 wm; apply/eqP; rewrite -(pexpr_eq1 m0) ?normr_ge0 //.
by rewrite -normrX wm normr1.
Qed.

Local Lemma unity_conj m w : (0 < m)%N -> w ^+ m = 1 -> w^* * w = 1.
Proof. by move=> m0 wm; rewrite -normCKC (unity_norm m0 wm) expr1n. Qed.

Local Lemma Re_le_N1 w : `|w| = 1 -> 'Re w <= -1 -> w = -1.
Proof.
move=> w1 Rw; have rN1 : (-1 : C) \is Num.real by rewrite rpredN real1.
have IN1 : 'Im (-1 : C) = 0 by apply/Creal_ImP.
have RN1 : 'Re (-1 : C) = -1 by apply/Creal_ReP.
apply: eqC_semipolar; rewrite ?normrN ?normr1 ?IN1 ?mulr0 //.
apply/le_anti; rewrite RN1 Rw /=.
have [] := leif_normC_Re_Creal w; rewrite w1 => le _.
by move: le; rewrite real_ler_norml ?Creal_Re // => /andP[].
Qed.

Local Lemma prim_root_existsC m :
  (0 < m)%N -> exists z : C, m.-primitive_root z.
Proof.
pose p : {poly C} := 'X^m - 1; have [r Dp] := closed_field_poly_normal p.
move=> m_gt0; rewrite (monicP _) ?monicXnsubC // scale1r in Dp.
have rn1 : all m.-unity_root r.
  by apply/allP=> z; rewrite -root_prod_XsubC -Dp.
have sz_r : (m < (size r).+1)%N.
  by rewrite -(size_prod_XsubC r id) -Dp size_XnsubC.
have [|z] := hasP (has_prim_root m_gt0 rn1 _ sz_r); last by exists z.
rewrite -separable_prod_XsubC -Dp.
by rewrite separable_Xn_sub_1 // pnatr_eq0 -lt0n.
Qed.

Local Lemma seq_Re_max (s : seq C) : s != [::] ->
  exists2 t, t \in s & forall w, w \in s -> 'Re w <= 'Re t.
Proof.
elim: s => // x [|y s] IH _.
  by exists x; rewrite ?mem_head // => w; rewrite inE => /eqP ->.
have [t ts tmax] := IH isT.
have /orP[xt|tx] := real_leVge (Creal_Re x) (Creal_Re t).
  exists t; first by rewrite inE ts orbT.
  by move=> w; rewrite inE => /orP[/eqP ->|/tmax].
exists x; first exact: mem_head.
move=> w; rewrite inE => /orP[/eqP -> //|/tmax wt]; exact: le_trans wt tx.
Qed.

Local Lemma N1_neq1 : (-1 : C) != 1.
Proof. by rewrite lt_eqF // (lt_trans _ ltr01) // ltrN10. Qed.

Local Lemma unity_argmax N : (0 < N)%N -> exists t,
  [/\ t ^+ (2 * N) = 1, 0 <= 'Im t, t != 1 &
      forall w, w ^+ (2 * N) = 1 -> 0 <= 'Im w -> w != 1 -> 'Re w <= 'Re t].
Proof.
move=> N0; pose p : {poly C} := 'X^(2 * N) - 1.
have [r Dp] := closed_field_poly_normal p.
rewrite (monicP _) ?monicXnsubC ?muln_gt0 // scale1r in Dp.
have rP w : (w \in r) = (w ^+ (2 * N) == 1).
  by rewrite -root_prod_XsubC -Dp /p rootE !hornerE subr_eq0.
pose P w := (0 <= 'Im w) && (w != 1).
have : filter P r != [::].
  apply/eqP => /(congr1 (fun s => -1 \in s)); rewrite mem_filter rP /P.
  have IN1 : 'Im (-1 : C) = 0 by apply/Creal_ImP; rewrite rpredN real1.
  by rewrite exprM sqrrN expr1n expr1n eqxx IN1 lexx N1_neq1 in_nil.
case/seq_Re_max => t; rewrite mem_filter /P rP.
move=> /andP[/andP[It t1] /eqP tN] tmax; exists t.
split=> // w /eqP wN Iw w1.
by apply: tmax; rewrite mem_filter /P rP Iw w1 wN.
Qed.

Section Descent.

Variables (m : nat) (t : C).
Hypotheses (m0 : (0 < m)%N) (tm : t ^+ m = 1) (It : 0 < 'Im t).
Hypothesis tmax :
  forall w, w ^+ m = 1 -> 0 <= 'Im w -> w != 1 -> 'Re w <= 'Re t.

Local Lemma descent_step w : w ^+ m = 1 -> 0 <= 'Im w -> w != 1 ->
  [/\ (w * t^*) ^+ m = 1, 0 <= 'Im (w * t^*) & 'Re w < 'Re (w * t^*)].
Proof.
move=> wm Iw w1; have wn := unity_norm m0 wm; have tn := unity_norm m0 tm.
have Iwt : 0 <= 'Im (w * t^*).
  apply: arc_Im => //; [by rewrite tn wn|exact: ltW|exact: tmax].
split=> //; first by rewrite exprMn -rmorphXn tm rmorph1 wm mulr1.
apply: arc_lt => //; first by rewrite normrM norm_conjC wn tn mulr1.
by rewrite rmorphM /= conjCK mulrA [w * _]mulrC (unity_conj m0 wm) mul1r.
Qed.

Local Lemma descent_chain w l : w ^+ m = 1 -> 0 <= 'Im w ->
  (forall j, (j < l)%N -> w * t^* ^+ j != 1) ->
  0 <= 'Im (w * t^* ^+ l) /\
  forall j, (j < l)%N -> 'Re (w * t^* ^+ j) < 'Re (w * t^* ^+ l).
Proof.
move=> wm Iw; elim: l => [_|l IH hl]; first by rewrite expr0 mulr1.
have [Il Rl] := IH (fun j jl => hl j (ltnW jl)).
have fm : (w * t^* ^+ l) ^+ m = 1.
  by rewrite exprMn -exprM mulnC exprM -rmorphXn tm rmorph1 expr1n wm mulr1.
have [_ I1 R1] := descent_step fm Il (hl l (ltnSn l)).
rewrite exprSr mulrA; split=> // j; rewrite ltnS leq_eqVlt.
by case/orP=> [/eqP -> //|/Rl jl]; exact: lt_trans jl R1.
Qed.

Local Lemma unity_descent w : w ^+ m = 1 -> 0 <= 'Im w -> exists i,
  [/\ w = t ^+ i, (i < m)%N & forall j, (j < i)%N -> w * t^* ^+ j != 1].
Proof.
move=> wm Iw.
have [k km wk] : exists2 k, (k < m)%N & w * t^* ^+ k == 1.
  case: (boolP [exists j : 'I_m, w * t^* ^+ j == 1]).
    by case/existsP => j wj; exists j.
  move=> /existsPn hn.
  have [_ /(_ 0%N m0)] := descent_chain wm Iw (fun j jm => hn (Ordinal jm)).
  by rewrite expr0 mulr1 -rmorphXn tm rmorph1 mulr1 ltxx.
have ex : exists j, w * t^* ^+ j == 1 by exists k.
have [i /eqP wi imin] := ex_minnP ex.
have tt : t^* ^+ i * t ^+ i = 1.
  by rewrite -exprMn (unity_conj m0 tm) expr1n.
exists i; split; first by rewrite -[w]mulr1 -tt mulrA wi mul1r.
  exact: leq_ltn_trans (imin k wk) km.
by move=> j ji; apply: contraTneq ji => wj; rewrite -leqNgt imin ?wj.
Qed.

End Descent.

Local Lemma unity_powers m t w : (0 < m)%N -> t ^+ m = 1 -> 0 <= 'Im t ->
  t != 1 ->
  (forall u, u ^+ m = 1 -> 0 <= 'Im u -> u != 1 -> 'Re u <= 'Re t) ->
  w ^+ m = 1 -> 0 <= 'Im w -> exists i, w = t ^+ i.
Proof.
move=> m0 tm It t1 tmax wm Iw.
have [It0|It0] := eqVneq ('Im t) 0; last first.
  have It1 : 0 < 'Im t by rewrite lt_def It0.
  by have [i [wi _ _]] := unity_descent m0 tm It1 tmax wm Iw; exists i.
have rt : t \is Num.real by apply/Creal_ImP.
have tN1 : t = -1.
  have : t ^+ 2 == 1 by rewrite -real_normK // (unity_norm m0 tm) expr1n.
  by rewrite sqrf_eq1 (negbTE t1) => /eqP.
have [-> | w1] := eqVneq w 1; first by exists 0%N.
exists 1%N; rewrite expr1 tN1; apply: Re_le_N1; first exact: unity_norm wm.
have := tmax _ wm Iw w1; rewrite tN1.
by have /Creal_ReP -> : (-1 : C) \is Num.real by rewrite rpredN real1.
Qed.

Local Lemma rootCN1_spec N : (0 < N)%N ->
  (2 * N).-primitive_root (N.-root (-1 : C)) /\
  forall w, w ^+ (2 * N) = 1 -> 0 <= 'Im w -> w != 1 ->
    'Re w <= 'Re (N.-root (-1 : C)).
Proof.
move=> N0; have [t [tm It t1 tmax]] := unity_argmax N0.
have m0 : (0 < 2 * N)%N by rewrite muln_gt0.
have [z zp] := prim_root_existsC m0; have zm := prim_expr_order zp.
have [z0 [z0m Iz0 z0d]] : exists z0, [/\ z0 ^+ (2 * N) = 1, 0 <= 'Im z0 &
    forall d, z0 ^+ d = 1 -> z ^+ d = 1].
  have r0 : (0 : C) \is Num.real by [].
  have /orP[Iz|Iz] := real_leVge r0 (Creal_Im z); first by exists z.
  exists z^*; rewrite -rmorphXn zm rmorph1 Im_conj oppr_ge0; split=> // d.
  by rewrite -rmorphXn => /(congr1 (fun x => x^*)); rewrite conjCK rmorph1.
have [i ti] := unity_powers m0 tm It t1 tmax z0m Iz0.
have tp : (2 * N).-primitive_root t.
  have [d dp dm] := prim_order_exists m0 tm.
  have md : (2 * N %| d)%N.
    by rewrite (prim_order_dvd zp) z0d // ti -exprM mulnC exprM
      (prim_expr_order dp) expr1n.
  suff -> : (2 * N)%N = d by [].
  by apply/eqP; rewrite eqn_dvd md dm.
have tN : t ^+ N = -1.
  have : (t ^+ N) ^+ 2 == 1 by rewrite -exprM mulnC tm.
  rewrite sqrf_eq1 => /orP[|/eqP //]; rewrite -(prim_order_dvd tp).
  by rewrite gtnNdvd // ltn_Pmull.
have -> : N.-root (-1) = t.
  apply: eq_rootC_Re_max => // u uN Iu; apply: tmax => //.
    by rewrite mulnC exprM uN sqrrN expr1n.
  apply/eqP => u1; move: uN; rewrite u1 expr1n => /eqP.
  by rewrite eq_sym (negbTE N1_neq1).
by [].
Qed.

Lemma rootCN1_prim n : (0 < n)%N ->
  (2 * n).-primitive_root (n.-root (-1 : C)).
Proof. by case/rootCN1_spec. Qed.

Lemma rootCN1_Re_max n w : (0 < n)%N -> w ^+ (2 * n) = 1 -> 0 <= 'Im w ->
  w != 1 -> 'Re w <= 'Re (n.-root (-1 : C)).
Proof. by move=> /rootCN1_spec[_]; apply. Qed.

Lemma Im_rootCN1_ge0 n : 0 <= 'Im (n.-root (-1 : C)).
Proof.
case: n => [|[|n]]; last by rewrite Im_rootC_ge0.
  by rewrite root0C; have /Creal_ImP -> : (0 : C) \is Num.real by [].
by rewrite root1C; have /Creal_ImP -> : (-1 : C) \is Num.real
  by rewrite rpredN real1.
Qed.

Lemma Im_rootCN1_gt0 n : (1 < n)%N -> 0 < 'Im (n.-root (-1 : C)).
Proof.
move=> n1; have n0 : (0 < n)%N by exact: ltnW.
rewrite lt_def Im_rootCN1_ge0 andbT; apply/eqP => /Creal_ImP rw.
have wp := rootCN1_prim n0; have wm := prim_expr_order wp.
have m0 : (0 < 2 * n)%N by rewrite muln_gt0.
have /eqP : n.-root (-1 : C) ^+ 2 = 1.
  by rewrite -real_normK // (unity_norm m0 wm) expr1n.
rewrite -(prim_order_dvd wp) => /dvdn_leq.
move=> /(_ isT); rewrite -{2}[2%N]muln1 leq_pmul2l //.
by rewrite leqNgt n1.
Qed.

Lemma rootCN1_index n k : (0 < n)%N -> (0 < k)%N ->
  (n * k).-root (-1 : C) ^+ k = n.-root (-1).
Proof.
move=> n0 k0; case: (ltnP 1 k) => [k1|k1]; last first.
  have -> : k = 1%N by apply/eqP; rewrite eqn_leq k1 k0.
  by rewrite muln1 expr1.
have N1 : (1 < n * k)%N by rewrite (leq_trans k1) // leq_pmull.
have N0 : (0 < n * k)%N := ltnW N1.
set t := (n * k).-root (-1 : C); set psi := n.-root (-1 : C).
have m0 : (0 < 2 * (n * k))%N by rewrite muln_gt0.
have tp := rootCN1_prim N0; have tm := prim_expr_order tp.
have It := Im_rootCN1_gt0 N1.
have tmax w := @rootCN1_Re_max (n * k) w N0.
have e2 : (2 * (n * k) = 2 * k * n)%N by rewrite [(n * k)%N]mulnC mulnA.
have psim : psi ^+ (2 * (n * k)) = 1.
  by rewrite mulnA exprM (prim_expr_order (rootCN1_prim n0)) expr1n.
have Ipsi := Im_rootCN1_ge0 n.
have [i [psii _ hi]] := unity_descent m0 tm It tmax psim Ipsi.
have psin : psi ^+ n = -1 by rewrite rootCK.
have tN : t ^+ (n * k) = -1 by rewrite rootCK.
have ik : (i %% (2 * k) = k)%N.
  have : t ^+ (i * n) == t ^+ (k * n).
    by rewrite exprM -psii psin [(k * n)%N]mulnC tN.
  rewrite (eq_prim_root_expr tp) e2 -!muln_modl eqn_pmul2r //.
  by rewrite (modn_small (_ : k < 2 * k)%N) ?ltn_Pmull // => /eqP.
have [q0|qpos] := posnP (i %/ (2 * k)).
  by move: psii; rewrite (divn_eq i (2 * k)) q0 mul0n add0n ik.
have ik2 : (2 * k < i)%N.
  by rewrite (divn_eq i (2 * k)) ik -addn1 leq_add // leq_pmull.
have [Iv Rv] := descent_chain m0 tm It tmax psim Ipsi
  (fun j jl => hi j (ltn_trans jl ik2)).
have k2 : (0 < 2 * k)%N by rewrite muln_gt0 k0.
have := Rv 0%N k2; rewrite expr0 mulr1.
have vn : (psi * t^* ^+ (2 * k)) ^+ n = -1.
  by rewrite exprMn psin -exprM -rmorphXn -e2 tm rmorph1 mulr1.
have := rootC_Re_max n0 vn Iv; rewrite -/psi => le lt.
by have := le_lt_trans le lt; rewrite ltxx.
Qed.




Local Lemma arc_conv p q : `|p| = `|q| -> 0 <= 'Im p -> 0 <= 'Im q ->
  0 <= 'Im (q * p^*) -> q != - p -> 'Re q <= 'Re p.
Proof.
move=> npq Ip Iq Iqp qp; rewrite real_leNgt ?Creal_Re //; apply/negP => pq.
have [p0|p0] := eqVneq p 0.
  have /normr0_eq0 q0 : `|q| = 0 by rewrite -npq p0 normr0.
  by move: pq; rewrite p0 q0 ltxx.
have := arc_Im (esym npq) Iq Ip (ltW pq).
have -> : p * q^* = (q * p^*)^* by rewrite rmorphM /= conjCK mulrC.
rewrite Im_conj oppr_ge0 => Iqp0.
have I0 : 'Im (q * p^*) = 0 by apply/le_anti; rewrite Iqp0.
have rz : q * p^* \is Num.real by apply/Creal_ImP.
have nz : `|q * p^*| = p * p^*.
  by rewrite normrM norm_conjC -npq -expr2 normCK.
have : (q * p^* - `|q * p^*|) * (q * p^* + `|q * p^*|) == 0.
  by rewrite -subr_sqr real_normK // subrr.
have pc0 : p^* != 0 by rewrite conjC_eq0.
rewrite mulf_eq0 subr_eq0 addr_eq0 nz -mulNr.
case/orP=> /eqP /(mulIf pc0) qE; first by move: pq; rewrite qE ltxx.
by rewrite qE eqxx in qp.
Qed.

Local Lemma Re_le_norm z : 'Re z <= `|z|.
Proof.
have [le _] := leif_normC_Re_Creal z.
exact: le_trans (real_ler_norm (Creal_Re z)) le.
Qed.

Local Lemma unit_real z : `|z| = 1 -> 'Im z = 0 -> z = 1 \/ z = -1.
Proof.
move=> z1 /Creal_ImP rz.
have : z ^+ 2 == 1 by rewrite -real_normK // z1 expr1n.
by rewrite sqrf_eq1 => /orP[] /eqP; [left|right].
Qed.

Local Lemma Re_unit1 z : `|z| = 1 -> 1 <= 'Re z -> z = 1.
Proof.
move=> z1 Rz; have R1 : 'Re (1 : C) = 1 by apply/Creal_ReP; rewrite real1.
have I1 : 'Im (1 : C) = 0 by apply/Creal_ImP; rewrite real1.
apply: eqC_semipolar; rewrite ?normr1 ?I1 ?mulr0 // R1.
by apply/le_anti; rewrite Rz -z1 Re_le_norm.
Qed.

Local Lemma arc_wrap s t : `|s| = 1 -> `|t| = 1 -> 0 <= 'Im s -> 0 <= 'Im t ->
  0 <= 'Im (s * t) -> 'Re (s * t) <= 'Re s -> 0 <= 'Re s + 'Re t.
Proof.
move=> sn tn Is It Ist Rst.
rewrite real_leNgt ?rpredD ?Creal_Re //; apply/negP => neg.
have Rs : 'Re s <= 'Re (- t^*).
  rewrite raddfN /= Re_conj -subr_ge0 -opprD oppr_ge0 addrC.
  exact: ltW.
have := arc_Im (p := - t^*) (q := s).
rewrite normrN norm_conjC sn tn raddfN /= Im_conj opprK.
move=> /(_ erefl It Is Rs); rewrite rmorphN /= conjCK mulrN raddfN /=.
rewrite oppr_ge0 => Ist0.
have I0 : 'Im (s * t) = 0 by apply/le_anti; rewrite Ist0.
have stn : `|s * t| = 1 by rewrite normrM sn tn mulr1.
have sc : s^* * s = 1 by rewrite -normCKC sn expr1n.
case: (unit_real stn I0) => st.
  have R1 : 'Re (1 : C) = 1 by apply/Creal_ReP; rewrite real1.
  have s1 : s = 1 by apply: Re_unit1 => //; move: Rst; rewrite st R1.
  move: st; rewrite s1 mul1r => t1.
  move: neg; rewrite s1 t1 R1 => neg.
  by have := lt_le_trans neg (addr_ge0 ler01 ler01); rewrite ltxx.
have tE : t = - s^* by rewrite -[t]mul1r -sc -mulrA st mulrN1.
by move: neg; rewrite tE raddfN /= Re_conj subrr ltxx.
Qed.

Local Lemma arc_T2 s t : `|s| = `|t| -> 0 <= 'Im s -> 0 <= 'Im t ->
  0 <= 'Re s + 'Re t -> 0 <= 'Im (s * t).
Proof.
move=> st Is It Rst.
have := arc_Im (p := s) (q := - t^*).
rewrite normrN norm_conjC st !raddfN /= Im_conj opprK Re_conj.
have Rts : - 'Re t <= 'Re s by rewrite -subr_ge0 opprK.
move=> /(_ erefl Is It Rts).
by rewrite mulNr -rmorphM /= raddfN /= Im_conj opprK mulrC.
Qed.

Local Lemma Re1C : 'Re (1 : C) = 1.
Proof. by apply/Creal_ReP; rewrite real1. Qed.

Local Lemma ReN1C : 'Re (-1 : C) = -1.
Proof. by apply/Creal_ReP; rewrite rpredN real1. Qed.

Local Lemma arc_sub A a : `|A| = 1 -> `|a| = 1 -> 0 <= 'Im A -> 0 <= 'Im a ->
  'Re A <= 'Re a -> 0 <= 'Im (A * a^*) /\ 'Re A <= 'Re (A * a^*).
Proof.
move=> An an IA Ia RAa.
have IP : 0 <= 'Im (A * a^*) by apply: arc_Im; rewrite ?an ?An.
split=> //.
have Ac : A * A^* = 1 by rewrite -normCK An expr1n.
have [AP|AP] := eqVneq A (- (A * a^*)); last first.
  apply: arc_conv => //; first by rewrite normrM norm_conjC An an mulr1.
  by rewrite rmorphM /= conjCK mulrA Ac mul1r.
have aN1 : a = -1.
  move/(congr1 (fun x => A^* * x)): AP.
  rewrite mulrN mulrA [A^* * A]mulrC Ac mul1r.
  move=> /(congr1 (fun x => - x^*)).
  by rewrite rmorph1 rmorphN /= conjCK opprK => <-.
have AN1 : A = -1 by apply: Re_le_N1 => //; rewrite -ReN1C -aN1.
rewrite AN1 aN1 rmorphN rmorph1 mulrNN mulr1 Re1C ReN1C.
exact: le_trans (lerN10 _) ler01.
Qed.

Local Lemma arc_add A B a b : `|A| = 1 -> `|B| = 1 -> `|a| = 1 -> `|b| = 1 ->
  0 <= 'Im A -> 0 <= 'Im B -> 0 <= 'Im a -> 0 <= 'Im b ->
  'Re A <= 'Re a -> 'Re B < 'Re b ->
  0 <= 'Im (A * B) -> 'Re (A * B) <= 'Re A ->
  0 <= 'Im (a * b) /\ 'Re (A * B) < 'Re (a * b).
Proof.
move=> An Bn an bn IA IB Ia Ib RAa RBb IAB RAB.
have nw := arc_wrap An Bn IA IB IAB RAB.
have Iab : 0 <= 'Im (a * b).
  apply: arc_T2; rewrite ?an ?bn //.
  exact: le_trans nw (lerD RAa (ltW RBb)).
split=> //.
have [IP RP] := arc_sub An an IA Ia RAa.
have [IQ RQ] := arc_sub Bn bn IB Ib (ltW RBb).
have ac : a^* * a = 1 by rewrite -normCKC an expr1n.
have bc : b^* * b = 1 by rewrite -normCKC bn expr1n.
have Pa : A * a^* * a = A by rewrite -mulrA ac mulr1.
have Qb : B * b^* * b = B by rewrite -mulrA bc mulr1.
move: (A * a^*) (B * b^*) IP RP IQ RQ Pa Qb => P Q IP RP IQ RQ Pa Qb.
have Pn : `|P| = 1 by move: An; rewrite -Pa normrM an mulr1.
have Qn : `|Q| = 1 by move: Bn; rewrite -Qb normrM bn mulr1.
have IPQ : 0 <= 'Im (P * Q).
  apply: arc_T2; rewrite ?Pn ?Qn //; exact: le_trans nw (lerD RP RQ).
have abn : `|a * b| = 1 by rewrite normrM an bn mulr1.
have abc : (a * b) * (a * b)^* = 1 by rewrite -normCK abn expr1n.
have ABE : A * B = P * Q * (a * b) by rewrite -Pa -Qb mulrACA.
have ABn : `|A * B| = 1 by rewrite normrM An Bn mulr1.
have Rle : 'Re (A * B) <= 'Re (a * b).
  have [E|E] := eqVneq (A * B) (- (a * b)); last first.
    apply: arc_conv => //; first by rewrite abn ABn.
    by rewrite ABE -mulrA abc mulr1.
  have I0 : 'Im (a * b) = 0.
    apply/le_anti; rewrite Iab andbT.
    by move: IAB; rewrite E raddfN oppr_ge0.
  case: (unit_real abn I0) => ab.
    by rewrite E ab raddfN /= Re1C; exact: le_trans (lerN10 _) ler01.
  move: RAB; rewrite E ab opprK Re1C => /(Re_unit1 An) A1.
  move: E; rewrite A1 mul1r ab opprK => B1.
  move: RBb; rewrite B1 Re1C => /lt_le_trans /(_ (Re_le_norm b)).
  by rewrite bn ltxx.
rewrite lt_neqAle Rle andbT; apply/eqP => ReE.
have ABab : A * B = a * b.
  by apply: eqC_semipolar; rewrite ?ABn ?abn ?mulr_ge0.
have PQ1 : P * Q = 1.
  by rewrite -[P * Q]mulr1 -abc mulrA -ABE ABab.
have Pc : P^* * P = 1 by rewrite -normCKC Pn expr1n.
have QE : Q = P^* by rewrite -[Q]mul1r -Pc -mulrA PQ1 mulr1.
have IP0 : 'Im P = 0.
  apply/le_anti; rewrite IP andbT.
  by move: IQ; rewrite QE Im_conj oppr_ge0.
case: (unit_real Pn IP0) => P1.
  by move: RBb; rewrite -Qb QE P1 rmorph1 mul1r ltxx.
have QN1 : Q = -1 by rewrite QE P1 rmorphN rmorph1.
move: (ler_ltD RAa RBb) nw; rewrite -Pa -Qb P1 QN1 !mulN1r !raddfN /=.
rewrite -opprD oppr_ge0 => lt le.
have h : 0 <= - ('Re a + 'Re b) by rewrite oppr_ge0.
by have := lt_le_trans lt (le_trans le h); rewrite ltxx.
Qed.

Local Lemma Im1C : 'Im (1 : C) = 0.
Proof. by apply/Creal_ImP; rewrite real1. Qed.

Local Lemma ImN1C : 'Im (-1 : C) = 0.
Proof. by apply/Creal_ImP; rewrite rpredN real1. Qed.

Local Lemma rootCN1_sector N i : (0 < N)%N -> (i <= N)%N ->
  0 <= 'Im (N.-root (-1 : C) ^+ i) /\
  forall j, (j < i)%N ->
    'Re (N.-root (-1 : C) ^+ i) < 'Re (N.-root (-1) ^+ j).
Proof.
move=> N0 iN; set t := N.-root (-1 : C).
have tp := rootCN1_prim N0; have tm := prim_expr_order tp.
have tN : t ^+ N = -1 by rewrite rootCK.
have m0 : (0 < 2 * N)%N by rewrite muln_gt0.
have [N1|N1] := leqP N 1.
  have N1' : N = 1%N by apply/eqP; rewrite eqn_leq N1 N0.
  move: iN tN; rewrite N1' expr1 => iN tN.
  case: i iN => [|[|//]] _; first by rewrite expr0 Im1C lexx.
  rewrite tN expr1 ImN1C lexx; split=> // j.
  rewrite ltnS leqn0 => /eqP ->.
  by rewrite expr0 ReN1C Re1C (lt_trans (ltrN10 _) ltr01).
have It := Im_rootCN1_gt0 N1.
have tmax w := @rootCN1_Re_max N w N0.
have wm : (-1 : C) ^+ (2 * N) = 1 by rewrite exprM sqrrN !expr1n.
have Iw : 0 <= 'Im (-1 : C) by rewrite ImN1C.
have tc : t * t^* = 1 by rewrite -normCK (unity_norm m0 tm) expr1n.
have hN j : (j < N)%N -> -1 * t^* ^+ j != 1.
  move=> jN; apply/eqP; rewrite mulN1r => /(congr1 (fun x => - x^*)).
  rewrite rmorphN /= opprK -rmorphXn /= conjCK rmorph1 -tN => /eqP.
  rewrite (eq_prim_root_expr tp) !modn_small ?(ltn_trans jN) ?ltn_Pmull //.
  by move=> /eqP jE; rewrite jE ltnn in jN.
have fl l : (l <= N)%N -> -1 * t^* ^+ l = t ^+ (N - l).
  move=> lN; rewrite -tN -{1}(subnK lN) exprD -mulrA -exprMn tc expr1n.
  by rewrite mulr1.
have hl l : (l <= N)%N -> forall j, (j < l)%N -> -1 * t^* ^+ j != 1.
  by move=> lN j jl; apply: hN; exact: leq_trans jl lN.
have [I _] := descent_chain m0 tm It tmax wm Iw (hl _ (leq_subr i N)).
rewrite fl ?leq_subr // subKn // in I; split=> // j ji.
have jN : (j <= N)%N by rewrite ltnW // (leq_trans ji).
have [_ R] := descent_chain m0 tm It tmax wm Iw (hl _ (leq_subr j N)).
have := R (N - i)%N (ltn_sub2l (leq_trans ji iN) ji).
by rewrite !fl ?leq_subr // !subKn.
Qed.

Local Lemma rootCN1_sqr_Re_max k w : (1 < k)%N -> w ^+ k = 1 -> 0 <= 'Im w ->
  w != 1 -> 'Re w <= 'Re (k.-root (-1 : C) ^+ 2).
Proof.
move=> k1 wk Iw w1; have k0 : (0 < k)%N by exact: ltnW.
set t := k.-root (-1 : C).
have tp := rootCN1_prim k0; have tm := prim_expr_order tp.
have m0 : (0 < 2 * k)%N by rewrite muln_gt0.
have It := Im_rootCN1_gt0 k1.
have tmax u := @rootCN1_Re_max k u k0.
have wm : w ^+ (2 * k) = 1 by rewrite mulnC exprM wk expr1n.
have [i [wi _ hi]] := unity_descent m0 tm It tmax wm Iw.
have i2 : (2 %| i)%N.
  have : t ^+ (i * k) == 1 by rewrite exprM -wi wk.
  by rewrite -(prim_order_dvd tp) dvdn_pmul2r.
have [i0|ipos] := posnP i; first by rewrite wi i0 expr0 eqxx in w1.
have [ie2|ine2] := eqVneq i 2%N; first by rewrite wi ie2.
have i2' : (2 < i)%N.
  by rewrite ltn_neqAle eq_sym ine2 dvdn_leq.
have tc : t^* * t = 1 by rewrite -normCKC (unity_norm m0 tm) expr1n.
have [_ R] := descent_chain m0 tm It tmax wm Iw (l := (i - 2)%N)
  (fun j ji => hi j (leq_trans ji (leq_subr _ _))).
have := R 0%N; rewrite subn_gt0 i2' expr0 mulr1 => /(_ isT) /ltW.
have E : w * t^* ^+ (i - 2) = t ^+ 2.
  rewrite wi -/t -{1}(subnK (ltnW i2')) exprD mulrAC -exprMn.
  by rewrite [t * _]mulrC tc expr1n mul1r.
by rewrite -/t E.
Qed.

Local Lemma rootC_arc N x : (2 < N)%N -> x != 0 ->
  [/\ `|N.-root x / `|N.-root x| | = 1,
      0 <= 'Im (N.-root x / `|N.-root x|)
    & 'Re (N.-root (-1 : C) ^+ 2) < 'Re (N.-root x / `|N.-root x|)].
Proof.
move=> N2 x0; have N1 : (1 < N)%N by exact: ltnW.
have N0 : (0 < N)%N by exact: ltnW.
have Ir : 0 <= 'Im (N.-root x) by rewrite Im_rootC_ge0.
set r := N.-root x in Ir *; set s := `|r|; set c := r / s.
set t := N.-root (-1 : C); set T := t ^+ 2.
have tp := rootCN1_prim N0; have tm := prim_expr_order tp.
have m0 : (0 < 2 * N)%N by rewrite muln_gt0.
have r0 : r != 0 by rewrite /r rootC_eq0.
have s0 : 0 < s by rewrite normr_gt0.
have sR : s \is Num.real by exact: gtr0_real.
have rs : r = s * c by rewrite /c mulrC divfK ?normr_eq0.
have cn : `|c| = 1 by rewrite normrM normfV normr_id divff ?normr_eq0.
have Ic : 0 <= 'Im c.
  by rewrite /c ImMr ?rpredV // mulr_ge0 ?invr_ge0 ?normr_ge0.
clearbody c s.
have Tn : `|T| = 1 by rewrite normrX (unity_norm m0 tm) expr1n.
have TN : T ^+ N = 1 by rewrite /T /t -exprM tm.
have [IT0 _] := rootCN1_sector (i := 2) N0 (ltnW N2).
have IT : 0 < 'Im T.
  rewrite lt_def IT0 andbT; apply/eqP => /(unit_real Tn) [] /eqP.
    rewrite /T /t -(prim_order_dvd tp) => /dvdn_leq h; move: (h isT).
    by rewrite -{2}[2%N]muln1 leq_pmul2l // leqNgt N1.
  rewrite -(rootCK N0 (-1)) /T /t (eq_prim_root_expr tp) !modn_small //.
    by move/eqP => N2'; rewrite N2' ltnn in N2.
    exact: (ltn_Pmull (isT : (1 < 2)%N) N0).
  exact: ltn_trans N2 (ltn_Pmull (isT : (1 < 2)%N) N0).
split=> //; rewrite real_ltNge ?Creal_Re //; apply/negP => cT.
have IcT : 0 <= 'Im (c * T^*) by apply: arc_Im; rewrite ?Tn ?cn.
have uN : (r * T^*) ^+ N = x.
  by rewrite exprMn -rmorphXn TN rmorph1 mulr1 rootCK.
have Iu : 0 <= 'Im (r * T^*).
  by rewrite rs -mulrA ImMl //; apply: mulr_ge0; [exact: ltW|exact: IcT].
have := rootC_Re_max N0 uN Iu; rewrite -/r rs -mulrA !(ReMl sR).
rewrite ler_pM2l // => Rle.
have cc : c * c^* = 1 by rewrite -normCK cn expr1n.
have := arc_lt (p := c * T^*) (q := c).
have E1 : `|c * T^*| = `|c| by rewrite normrM norm_conjC Tn mulr1.
have E2 : c * (c * T^*)^* = T by rewrite rmorphM /= conjCK mulrA cc mul1r.
rewrite E1 E2 => /(_ erefl IcT Ic IT) lt.
by have := le_lt_trans Rle lt; rewrite ltxx.
Qed.

Lemma exp_rootC_mul n k (x : C) : (0 < n)%N ->
  (n * k).-root x ^+ n = k.-root x.
Proof.
move=> n0; have e0 : (0 : C) ^+ n = 0 by rewrite expr0n eqn0Ngt n0.
case: k => [|k]; first by rewrite muln0 !root0C e0.
case: k => [|k]; first by rewrite muln1 rootCK // root1C.
have [n1|n1] := leqP n 1.
  have -> : n = 1%N by apply/eqP; rewrite eqn_leq n1 n0.
  by rewrite mul1n expr1.
have [->|x0] := eqVneq x 0; first by rewrite !rootC0 e0.
set k2 := k.+2; have k1 : (1 < k2)%N by [].
have k0 : (0 < k2)%N by [].
have N0 : (0 < n * k2)%N by rewrite muln_gt0 n0.
have N2 : (2 < n * k2)%N.
  by rewrite (leq_trans _ (leq_mul n1 k1)).
have [cn Ic RTc] := rootC_arc N2 x0.
set r := (n * k2).-root x in cn Ic RTc *; set s := `|r| in cn Ic RTc *.
set c := r / s in cn Ic RTc *.
set t := (n * k2).-root (-1 : C) in RTc *; set T := t ^+ 2 in RTc *.
have r0 : r != 0 by rewrite /r rootC_eq0.
have s0 : 0 < s by rewrite normr_gt0.
have sR : s \is Num.real by exact: gtr0_real.
have rs : r = s * c by rewrite /c mulrC divfK ?normr_eq0.
clearbody c.
have m0 : (0 < 2 * (n * k2))%N by rewrite muln_gt0.
have tm := prim_expr_order (rootCN1_prim N0).
have Tn : `|T| = 1 by rewrite normrX (unity_norm m0 tm) expr1n.
have TjE j : T ^+ j = t ^+ (2 * j) by rewrite /T -exprM.
have jN j : (j <= n)%N -> (2 * j <= n * k2)%N.
  by move=> jn; rewrite mulnC leq_mul.
have IT j : (j <= n)%N -> 0 <= 'Im (T ^+ j).
  by move=> jn; have [I _] := rootCN1_sector N0 (jN j jn); rewrite TjE.
have RT j : (j < n)%N -> 'Re (T ^+ j.+1) < 'Re (T ^+ j).
  move=> jn; have [_ R] := rootCN1_sector N0 (jN _ jn).
  by rewrite !TjE R // ltn_pmul2l.
have chain j : (0 < j)%N -> (j <= n)%N ->
    0 <= 'Im (c ^+ j) /\ 'Re (T ^+ j) < 'Re (c ^+ j).
  elim: j => // -[_ _ _|j IH _ jn]; first by rewrite !expr1.
  have [Icj Rj] := IH isT (ltnW jn).
  have := arc_add (A := T ^+ j.+1) (B := T) (a := c ^+ j.+1) (b := c).
  have TjN : `|T ^+ j.+1| = 1 by rewrite normrX Tn expr1n.
  have cjN : `|c ^+ j.+1| = 1 by rewrite normrX cn expr1n.
  have IT1 : 0 <= 'Im T by have := IT 1%N (ltnW n1); rewrite expr1.
  rewrite -!exprSr => /(_ TjN Tn cjN cn (IT _ (ltnW jn)) IT1 Icj Ic (ltW Rj)).
  by move=> /(_ RTc (IT _ jn) (ltW (RT _ jn))).
have [Icn Rn] := chain n n0 (leqnn n).
have tau : T ^+ n = k2.-root (-1) ^+ 2.
  rewrite /T -exprM mulnC exprM /t [(n * k2)%N]mulnC.
  by rewrite (rootCN1_index k0 n0).
have sn0 : 0 < s ^+ n by rewrite exprn_gt0.
have snR : s ^+ n \is Num.real by exact: gtr0_real.
have rn : r ^+ n = s ^+ n * c ^+ n by rewrite rs exprMn.
symmetry; apply: eq_rootC_Re_max => //; first by rewrite -exprM rootCK.
  by rewrite rn ImMl //; apply: mulr_ge0; [exact: ltW|exact: Icn].
move=> v vk Iv.
have v0 : v != 0 by apply: contraNneq x0 => v0; rewrite -vk v0 expr0n.
have vn : `|v| = s ^+ n.
  apply/eqP; rewrite -(eqrXn2 k0) ?normr_ge0 ?exprn_ge0 ?ltW //.
  by rewrite -normrX vk -[x](rootCK N0) normrX -exprM.
have en : `|v / `|v| | = 1.
  by rewrite normrM normfV normr_id divff ?normr_eq0.
have Ie : 0 <= 'Im (v / `|v|).
  by rewrite ImMr ?rpredV ?normr_real // mulr_ge0 ?invr_ge0 ?normr_ge0.
have ve : v = s ^+ n * (v / `|v|) by rewrite -vn mulrC divfK ?normr_eq0.
move: (v / `|v|) en Ie ve => e en Ie ve.
rewrite rn ve !(ReMl snR) ler_pM2l //.
rewrite real_leNgt ?Creal_Re //; apply/negP => lt.
have cnN : `|c ^+ n| = 1 by rewrite normrX cn expr1n.
have [Irho Rrho] := arc_sub cnN en Icn Ie (ltW lt).
have ek : e ^+ k2 = (c ^+ n) ^+ k2.
  have sk0 : (s ^+ n) ^+ k2 != 0 by rewrite expf_neq0 ?gt_eqF.
  apply: (mulfI sk0); rewrite -!exprMn -ve -rs vk -exprM.
  by rewrite rootCK.
have ec : e^* * e = 1 by rewrite -normCKC en expr1n.
have zn : `|(c ^+ n) ^+ k2| = 1 by rewrite normrX cnN expr1n.
have rhok : (c ^+ n * e^*) ^+ k2 = 1.
  by rewrite exprMn -rmorphXn ek -normCK zn expr1n.
have rho1 : c ^+ n * e^* != 1.
  apply: contraTneq lt => rho1.
  have ce : c ^+ n = e by rewrite -[c ^+ n]mulr1 -ec mulrA rho1 mul1r.
  by rewrite ce ltxx.
have := rootCN1_sqr_Re_max k1 rhok Irho rho1; rewrite -tau => le.
by have := lt_le_trans Rn (le_trans Rrho le); rewrite ltxx.
Qed.

Lemma rootC_mul n k (x : C) : (n * k).-root x = n.-root (k.-root x).
Proof.
case: n => [|[|n]]; first by rewrite mul0n !root0C.
  by rewrite mul1n root1C.
case: k => [|k]; first by rewrite muln0 !root0C rootC0.
set n2 := n.+2; set k1 := k.+1.
have n0 : (0 < n2)%N by [].
have N0 : (0 < n2 * k1)%N by rewrite muln_gt0.
have N1 : (1 < n2 * k1)%N by rewrite (leq_trans _ (leq_pmulr _ _)).
rewrite -(exp_rootC_mul k1 x n0); set r := (n2 * k1).-root x.
symmetry; apply: eq_rootC_Re_max => //; first by rewrite Im_rootC_ge0.
move=> u un Iu; apply: rootC_Re_max N0 _ Iu.
by rewrite exprM un -exprM rootCK.
Qed.

End NthRootUnity.
