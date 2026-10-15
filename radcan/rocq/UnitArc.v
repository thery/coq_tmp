(******************************************************************************)
(* UnitArc: the principal roots of -1 on a numClosedFieldType C, proved       *)
(* without trigonometry.  omega_n := n.-root (-1 : C)  (= e^{i pi / n}).      *)
(*                                                                            *)
(*   arc_Im     : |p| = |q|, 0 <= 'Im p, 0 <= 'Im q, 'Re q <= 'Re p           *)
(*                imply 0 <= 'Im (q * conj p)                                 *)
(*   arc_lt     : same points, 0 < 'Im (q * conj p) -> 'Re q < 'Re p          *)
(*   prim_root_existsC : C has a primitive m-th root of unity (0 < m)         *)
(*   unity_argmax : among the 2N-th roots of unity w <> 1 with 0 <= 'Im w,    *)
(*                some t has the largest real part                            *)
(*   descent_chain, unity_descent : for such a t with 0 < 'Im t, every root   *)
(*                of unity w with 0 <= 'Im w is t ^+ i, and w * conj t ^+ j   *)
(*                (j <= i) stays in 0 <= 'Im with increasing real part        *)
(*   unity_powers : the same conclusion w = t ^+ i, also when 'Im t = 0       *)
(*   rootC_N1_spec, rootC_N1_max : omega_N is that t: it has the largest      *)
(*                real part among the 2N-th roots of unity w <> 1, 0 <= 'Im w *)
(*   rootC_N1_prim  : (2 * n).-primitive_root omega_n          (0 < n)        *)
(*   Im_rootC_N1_ge0, Im_rootC_N1_gt0 : 0 <= 'Im omega_n, 0 < ... (1 < n)     *)
(*   rootC_N1_index : omega_(n * k) ^+ k = omega_n             (0 < n, k)     *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require cyclic separable cyclotomic.
From Radcan Require Import OmegaC.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section UnitArc.

Variable C : numClosedFieldType.
Implicit Types (p q t w z : C).

Lemma arc_Im p q : `|p| = `|q| -> 0 <= 'Im p -> 0 <= 'Im q ->
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

Lemma arc_lt p q : `|p| = `|q| -> 0 <= 'Im p -> 0 <= 'Im q ->
  0 < 'Im (q * p^*) -> 'Re q < 'Re p.
Proof.
move=> npq Ip Iq Iqp; rewrite real_ltNge ?Creal_Re //; apply/negP => pq.
have := arc_Im (esym npq) Iq Ip pq.
have -> : p * q^* = (q * p^*)^* by rewrite rmorphM /= conjCK mulrC.
rewrite Im_conj oppr_ge0 => h.
by have := lt_le_trans Iqp h; rewrite ltxx.
Qed.

Lemma unity_norm m w : (0 < m)%N -> w ^+ m = 1 -> `|w| = 1.
Proof.
move=> m0 wm; apply/eqP; rewrite -(pexpr_eq1 m0) ?normr_ge0 //.
by rewrite -normrX wm normr1.
Qed.

Lemma unity_conj m w : (0 < m)%N -> w ^+ m = 1 -> w^* * w = 1.
Proof. by move=> m0 wm; rewrite -normCKC (unity_norm m0 wm) expr1n. Qed.

Lemma Re_le_N1 w : `|w| = 1 -> 'Re w <= -1 -> w = -1.
Proof.
move=> w1 Rw; have rN1 : (-1 : C) \is Num.real by rewrite rpredN real1.
have IN1 : 'Im (-1 : C) = 0 by apply/Creal_ImP.
have RN1 : 'Re (-1 : C) = -1 by apply/Creal_ReP.
apply: eqC_semipolar; rewrite ?normrN ?normr1 ?IN1 ?mulr0 //.
apply/le_anti; rewrite RN1 Rw /=.
have [] := leif_normC_Re_Creal w; rewrite w1 => le _.
by move: le; rewrite real_ler_norml ?Creal_Re // => /andP[].
Qed.

Lemma prim_root_existsC m : (0 < m)%N -> exists z : C, m.-primitive_root z.
Proof.
pose p : {poly C} := 'X^m - 1; have [r Dp] := closed_field_poly_normal p.
move=> m_gt0; rewrite (monicP _) ?monicXnsubC // scale1r in Dp.
have rn1 : all m.-unity_root r.
  by apply/allP=> z; rewrite -root_prod_XsubC -Dp.
have sz_r : (m < (size r).+1)%N.
  by rewrite -(size_prod_XsubC r id) -Dp size_XnsubC.
have [|z] := hasP (cyclic.has_prim_root m_gt0 rn1 _ sz_r); last by exists z.
rewrite -separable.separable_prod_XsubC -Dp.
by rewrite cyclotomic.separable_Xn_sub_1 // pnatr_eq0 -lt0n.
Qed.

Lemma seq_Re_max (s : seq C) : s != [::] ->
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

Lemma N1_neq1 : (-1 : C) != 1.
Proof. by rewrite lt_eqF // (lt_trans _ ltr01) // ltrN10. Qed.

Lemma unity_argmax N : (0 < N)%N -> exists t,
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

Lemma descent_step w : w ^+ m = 1 -> 0 <= 'Im w -> w != 1 ->
  [/\ (w * t^*) ^+ m = 1, 0 <= 'Im (w * t^*) & 'Re w < 'Re (w * t^*)].
Proof.
move=> wm Iw w1; have wn := unity_norm m0 wm; have tn := unity_norm m0 tm.
have Iwt : 0 <= 'Im (w * t^*).
  apply: arc_Im => //; [by rewrite tn wn|exact: ltW|exact: tmax].
split=> //; first by rewrite exprMn -rmorphXn tm rmorph1 wm mulr1.
apply: arc_lt => //; first by rewrite normrM norm_conjC wn tn mulr1.
by rewrite rmorphM /= conjCK mulrA [w * _]mulrC (unity_conj m0 wm) mul1r.
Qed.

Lemma descent_chain w l : w ^+ m = 1 -> 0 <= 'Im w ->
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

Lemma unity_descent w : w ^+ m = 1 -> 0 <= 'Im w -> exists i,
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

Lemma unity_powers m t w : (0 < m)%N -> t ^+ m = 1 -> 0 <= 'Im t ->
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

Lemma rootC_N1_spec N : (0 < N)%N ->
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
  apply: rootC_char => // u uN Iu; apply: tmax => //.
    by rewrite mulnC exprM uN sqrrN expr1n.
  apply/eqP => u1; move: uN; rewrite u1 expr1n => /eqP.
  by rewrite eq_sym (negbTE N1_neq1).
by [].
Qed.

Lemma rootC_N1_prim n : (0 < n)%N ->
  (2 * n).-primitive_root (n.-root (-1 : C)).
Proof. by case/rootC_N1_spec. Qed.

Lemma rootC_N1_max n w : (0 < n)%N -> w ^+ (2 * n) = 1 -> 0 <= 'Im w ->
  w != 1 -> 'Re w <= 'Re (n.-root (-1 : C)).
Proof. by move=> /rootC_N1_spec[_]; apply. Qed.

Lemma Im_rootC_N1_ge0 n : 0 <= 'Im (n.-root (-1 : C)).
Proof.
case: n => [|[|n]]; last by rewrite Im_rootC_ge0.
  by rewrite root0C; have /Creal_ImP -> : (0 : C) \is Num.real by [].
by rewrite root1C; have /Creal_ImP -> : (-1 : C) \is Num.real
  by rewrite rpredN real1.
Qed.

Lemma Im_rootC_N1_gt0 n : (1 < n)%N -> 0 < 'Im (n.-root (-1 : C)).
Proof.
move=> n1; have n0 : (0 < n)%N by exact: ltnW.
rewrite lt_def Im_rootC_N1_ge0 andbT; apply/eqP => /Creal_ImP rw.
have wp := rootC_N1_prim n0; have wm := prim_expr_order wp.
have m0 : (0 < 2 * n)%N by rewrite muln_gt0.
have /eqP : n.-root (-1 : C) ^+ 2 = 1.
  by rewrite -real_normK // (unity_norm m0 wm) expr1n.
rewrite -(prim_order_dvd wp) => /dvdn_leq.
move=> /(_ isT); rewrite -{2}[2%N]muln1 leq_pmul2l //.
by rewrite leqNgt n1.
Qed.

Lemma rootC_N1_index n k : (0 < n)%N -> (0 < k)%N ->
  (n * k).-root (-1 : C) ^+ k = n.-root (-1).
Proof.
move=> n0 k0; case: (ltnP 1 k) => [k1|k1]; last first.
  have -> : k = 1%N by apply/eqP; rewrite eqn_leq k1 k0.
  by rewrite muln1 expr1.
have N1 : (1 < n * k)%N by rewrite (leq_trans k1) // leq_pmull.
have N0 : (0 < n * k)%N := ltnW N1.
set t := (n * k).-root (-1 : C); set psi := n.-root (-1 : C).
have m0 : (0 < 2 * (n * k))%N by rewrite muln_gt0.
have tp := rootC_N1_prim N0; have tm := prim_expr_order tp.
have It := Im_rootC_N1_gt0 N1.
have tmax w := @rootC_N1_max (n * k) w N0.
have e2 : (2 * (n * k) = 2 * k * n)%N by rewrite [(n * k)%N]mulnC mulnA.
have psim : psi ^+ (2 * (n * k)) = 1.
  by rewrite mulnA exprM (prim_expr_order (rootC_N1_prim n0)) expr1n.
have Ipsi := Im_rootC_N1_ge0 n.
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

End UnitArc.
