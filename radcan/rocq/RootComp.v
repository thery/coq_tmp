(******************************************************************************)
(* RootComp: composition of mathcomp's principal roots on a                   *)
(* numClosedFieldType C, for every x (no hypothesis on the argument of x).    *)
(*                                                                            *)
(*   rootC_mul   : (n * k).-root x = n.-root (k.-root x)                      *)
(*   rootC_mulnX : (n * k).-root x ^+ n = k.-root x              (0 < n)      *)
(*                                                                            *)
(* Angle calculus on the closed upper half unit circle, without trigonometry  *)
(* (u is before v when 'Re v <= 'Re u):                                       *)
(*   arc_conv  : converse of arc_Im (UnitArc.v), except for q = - p           *)
(*   arc_T2    : 0 <= 'Re s + 'Re t gives 0 <= 'Im (s * t)                    *)
(*   arc_wrap  : s * t in 0 <= 'Im, after s, implies 0 <= 'Re s + 'Re t       *)
(*   arc_sub   : a before A gives A * a^* in 0 <= 'Im, after A                *)
(*   arc_add   : a before A, b strictly before B, A * B after A (no wrap)     *)
(*               imply a * b strictly before A * B                            *)
(*   rootC_N1_sector : omega_N ^+ i (i <= N) stay in 0 <= 'Im with strictly   *)
(*               decreasing real part                                         *)
(*   rootC_N1_sqr_max : omega_k ^+ 2 has the largest real part among the      *)
(*               k-th roots of unity w <> 1 with 0 <= 'Im w      (1 < k)      *)
(*   rootC_arc : the unit c = N.-root x / |N.-root x| (x <> 0, 2 < N) lies    *)
(*               strictly before omega_N ^+ 2 on the upper half circle        *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import OmegaC UnitArc.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section RootComp.

Variable C : numClosedFieldType.
Implicit Types (p q t w z a b A B : C).

Lemma arc_conv p q : `|p| = `|q| -> 0 <= 'Im p -> 0 <= 'Im q ->
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

Lemma Re_le_norm z : 'Re z <= `|z|.
Proof.
have [le _] := leif_normC_Re_Creal z.
exact: le_trans (real_ler_norm (Creal_Re z)) le.
Qed.

Lemma unit_real z : `|z| = 1 -> 'Im z = 0 -> z = 1 \/ z = -1.
Proof.
move=> z1 /Creal_ImP rz.
have : z ^+ 2 == 1 by rewrite -real_normK // z1 expr1n.
by rewrite sqrf_eq1 => /orP[] /eqP; [left|right].
Qed.

Lemma Re_unit1 z : `|z| = 1 -> 1 <= 'Re z -> z = 1.
Proof.
move=> z1 Rz; have R1 : 'Re (1 : C) = 1 by apply/Creal_ReP; rewrite real1.
have I1 : 'Im (1 : C) = 0 by apply/Creal_ImP; rewrite real1.
apply: eqC_semipolar; rewrite ?normr1 ?I1 ?mulr0 // R1.
by apply/le_anti; rewrite Rz -z1 Re_le_norm.
Qed.

Lemma arc_wrap s t : `|s| = 1 -> `|t| = 1 -> 0 <= 'Im s -> 0 <= 'Im t ->
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

Lemma arc_T2 s t : `|s| = `|t| -> 0 <= 'Im s -> 0 <= 'Im t ->
  0 <= 'Re s + 'Re t -> 0 <= 'Im (s * t).
Proof.
move=> st Is It Rst.
have := arc_Im (p := s) (q := - t^*).
rewrite normrN norm_conjC st !raddfN /= Im_conj opprK Re_conj.
have Rts : - 'Re t <= 'Re s by rewrite -subr_ge0 opprK.
move=> /(_ erefl Is It Rts).
by rewrite mulNr -rmorphM /= raddfN /= Im_conj opprK mulrC.
Qed.

Lemma Re1C : 'Re (1 : C) = 1.
Proof. by apply/Creal_ReP; rewrite real1. Qed.

Lemma ReN1C : 'Re (-1 : C) = -1.
Proof. by apply/Creal_ReP; rewrite rpredN real1. Qed.

Lemma arc_sub A a : `|A| = 1 -> `|a| = 1 -> 0 <= 'Im A -> 0 <= 'Im a ->
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

Lemma arc_add A B a b : `|A| = 1 -> `|B| = 1 -> `|a| = 1 -> `|b| = 1 ->
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

Lemma Im1C : 'Im (1 : C) = 0.
Proof. by apply/Creal_ImP; rewrite real1. Qed.

Lemma ImN1C : 'Im (-1 : C) = 0.
Proof. by apply/Creal_ImP; rewrite rpredN real1. Qed.

Lemma rootC_N1_sector N i : (0 < N)%N -> (i <= N)%N ->
  0 <= 'Im (N.-root (-1 : C) ^+ i) /\
  forall j, (j < i)%N ->
    'Re (N.-root (-1 : C) ^+ i) < 'Re (N.-root (-1) ^+ j).
Proof.
move=> N0 iN; set t := N.-root (-1 : C).
have tp := rootC_N1_prim C N0; have tm := prim_expr_order tp.
have tN : t ^+ N = -1 by rewrite rootCK.
have m0 : (0 < 2 * N)%N by rewrite muln_gt0.
have [N1|N1] := leqP N 1.
  have N1' : N = 1%N by apply/eqP; rewrite eqn_leq N1 N0.
  move: iN tN; rewrite N1' expr1 => iN tN.
  case: i iN => [|[|//]] _; first by rewrite expr0 Im1C lexx.
  rewrite tN expr1 ImN1C lexx; split=> // j.
  rewrite ltnS leqn0 => /eqP ->.
  by rewrite expr0 ReN1C Re1C (lt_trans (ltrN10 _) ltr01).
have It := Im_rootC_N1_gt0 C N1.
have tmax w := @rootC_N1_max C N w N0.
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

Lemma rootC_N1_sqr_max k w : (1 < k)%N -> w ^+ k = 1 -> 0 <= 'Im w ->
  w != 1 -> 'Re w <= 'Re (k.-root (-1 : C) ^+ 2).
Proof.
move=> k1 wk Iw w1; have k0 : (0 < k)%N by exact: ltnW.
set t := k.-root (-1 : C).
have tp := rootC_N1_prim C k0; have tm := prim_expr_order tp.
have m0 : (0 < 2 * k)%N by rewrite muln_gt0.
have It := Im_rootC_N1_gt0 C k1.
have tmax u := @rootC_N1_max C k u k0.
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

Lemma rootC_arc N x : (2 < N)%N -> x != 0 ->
  [/\ `|N.-root x / `|N.-root x| | = 1,
      0 <= 'Im (N.-root x / `|N.-root x|)
    & 'Re (N.-root (-1 : C) ^+ 2) < 'Re (N.-root x / `|N.-root x|)].
Proof.
move=> N2 x0; have N1 : (1 < N)%N by exact: ltnW.
have N0 : (0 < N)%N by exact: ltnW.
have Ir : 0 <= 'Im (N.-root x) by rewrite Im_rootC_ge0.
set r := N.-root x in Ir *; set s := `|r|; set c := r / s.
set t := N.-root (-1 : C); set T := t ^+ 2.
have tp := rootC_N1_prim C N0; have tm := prim_expr_order tp.
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
have [IT0 _] := rootC_N1_sector (i := 2) N0 (ltnW N2).
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

Lemma rootC_mulnX n k (x : C) : (0 < n)%N ->
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
have tm := prim_expr_order (rootC_N1_prim C N0).
have Tn : `|T| = 1 by rewrite normrX (unity_norm m0 tm) expr1n.
have TjE j : T ^+ j = t ^+ (2 * j) by rewrite /T -exprM.
have jN j : (j <= n)%N -> (2 * j <= n * k2)%N.
  by move=> jn; rewrite mulnC leq_mul.
have IT j : (j <= n)%N -> 0 <= 'Im (T ^+ j).
  by move=> jn; have [I _] := rootC_N1_sector N0 (jN j jn); rewrite TjE.
have RT j : (j < n)%N -> 'Re (T ^+ j.+1) < 'Re (T ^+ j).
  move=> jn; have [_ R] := rootC_N1_sector N0 (jN _ jn).
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
  by rewrite (rootC_N1_index C k0 n0).
have sn0 : 0 < s ^+ n by rewrite exprn_gt0.
have snR : s ^+ n \is Num.real by exact: gtr0_real.
have rn : r ^+ n = s ^+ n * c ^+ n by rewrite rs exprMn.
symmetry; apply: rootC_char => //; first by rewrite -exprM rootCK.
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
have := rootC_N1_sqr_max k1 rhok Irho rho1; rewrite -tau => le.
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
rewrite -(rootC_mulnX k1 x n0); set r := (n2 * k1).-root x.
symmetry; apply: rootC_char => //; first by rewrite Im_rootC_ge0.
move=> u un Iu; apply: rootC_Re_max N0 _ Iu.
by rewrite exprM un -exprM rootCK.
Qed.

End RootComp.
