(******************************************************************************)
(* GaussSum: the sign of the quadratic Gauss sum (Gauss), on a                *)
(* numClosedFieldType C with the principal roots of mathcomp, no analysis.    *)
(*   omega_n := n.-root (-1)  (= e^(i pi/n)),  zeta_n := omega_n ^+ 2,        *)
(*   gauss_sum n := sum_(a < n) zeta_n ^+ (a * a).                            *)
(*                                                                            *)
(* Route (Gauss's own proof, purely algebraic):                               *)
(*   qbin q m k     : the Gaussian binomial [m, k]_q (q-Pascal recursion)     *)
(*   qalt_even      : sum_k (-1)^k [2t, k]_q = prod_(j < t) (1 - q^(2j+1))    *)
(*   qbin_root      : [n-1, k]_q = (-1)^k r^C(k+1,2), q r = 1, q primitive    *)
(*   gauss_prod     : sum_(a < n) z^(a a) = prod_(j < n/2) (z^(2j+1) -        *)
(*                    z^-(2j+1)), z a primitive n-th root, n odd (any field)  *)
(*   prod_one_sub_root : prod_(k = 1 .. n-1) (1 - z^k) = n                    *)
(*   gauss_prod_sqr : (that product) ^ 2 = (-1)^(n/2) n                       *)
(* Sign (RootComp.v, UnitArc.v, no trigonometry): each factor is 'i times a   *)
(* real 2 'Im (omega_n ^ (4j+2)), positive iff 4j+2 < n                       *)
(*   Im_rootC_N1_expr_gt0 / _lt0 : sign of 'Im omega_n ^ k, 0<k<n / n<k<2n    *)
(*   gauss_sumC      : gauss_sum n = 'i ^+ odd (n/2) * sqrtC n   (n odd)      *)
(*   gauss_sum_sqr   : gauss_sum n ^ 2 = (-1)^(n/2) n             (n odd)     *)
(*   gauss_sum_1mod4 : n = 1 mod 4 -> gauss_sum n = sqrtC n                   *)
(*   gauss_sum_3mod4 : n = 3 mod 4 -> gauss_sum n = 'i * sqrtC n              *)
(*   gauss_sum_prime : the same for an odd prime p, as one if-statement       *)
(*   sqrtC_gauss_1mod4 : sqrtC n = sum_(a<n) omega_n ^ (2 a^2 mod 2n)         *)
(*   sqrtC_gauss_3mod4 : sqrtC n = sum_(a<n) omega_2n ^ ((3n + 4a^2) mod 4n)  *)
(*   (sqrtC 2 = omega_4 - omega_4 ^ 3 is omega4_sqrt2C in OmegaC.v)           *)
(******************************************************************************)

From Stdlib Require Import Lia.
From mathcomp Require Import all_boot all_order all_algebra zify.
From Radcan Require Import OmegaC UnitArc RootComp.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section QBin.

Variables (R : comNzRingType) (q : R).

Fixpoint qbin (m k : nat) : R :=
  match m, k with
  | 0%N, 0%N => 1
  | 0%N, _.+1 => 0
  | _.+1, 0%N => 1
  | m'.+1, k'.+1 => qbin m' k' + q ^+ k'.+1 * qbin m' k'.+1
  end.

Lemma qbinn0 m : qbin m 0 = 1. Proof. by case: m. Qed.

Lemma qbinSS m k : qbin m.+1 k.+1 = qbin m k + q ^+ k.+1 * qbin m k.+1.
Proof. by []. Qed.

Lemma qbin_small m k : (m < k)%N -> qbin m k = 0.
Proof.
elim: m k => [|m IH] [|k] //= mk.
by rewrite !IH ?mulr0 ?addr0 // ltnW.
Qed.

Lemma qbin_ratio m k :
  (1 - q ^+ (m - k)) * qbin m k = (1 - q ^+ k.+1) * qbin m k.+1.
Proof.
elim: m k => [|m IH] [|k] /=.
- by rewrite subrr mul0r mulr0.
- by rewrite !mulr0.
- have := IH 0%N; rewrite qbinn0 subn0 !mulr1 !expr1 => E.
  rewrite mulrDr mulr1 mulrCA -E mulrBr mulr1 -exprS.
  by rewrite addrA subrK.
have [km|mk] := ltnP k m; last first.
  have z1 : qbin m k.+1 = 0 by apply: qbin_small.
  have z2 : qbin m k.+2 = 0 by apply: qbin_small; rewrite ltnW.
  rewrite z1 z2 !mulr0 add0r addr0.
  by rewrite subSS (eqP mk) expr0 subrr mul0r mulr0.
have := IH k; have := IH k.+1.
rewrite subSS -(subnSK km) => E2 E1.
set d := (m - k.+1)%N in E1 E2 *.
rewrite mulrDr E1 mulrCA mulrA -mulrDl.
rewrite [RHS]mulrDr [X in _ = _ + X]mulrCA -E2 mulrA -mulrDl.
congr (_ * _).
by rewrite !mulrBr !mulr1 -!exprD !addrA !subrK addnS addSn.
Qed.

Lemma qbin_absorb m k :
  (1 - q ^+ k.+1) * qbin m.+1 k.+1 = (1 - q ^+ m.+1) * qbin m k.
Proof.
have [mk|km] := ltnP m k.
  by rewrite !qbin_small ?mulr0 // ltnS.
rewrite qbinSS mulrDr mulrCA -qbin_ratio mulrA -mulrDl; congr (_ * _).
by rewrite mulrBr mulr1 -exprD addrA subrK addSn subnKC.
Qed.

(* the alternating sum of a row of q-binomials *)
Definition qalt m := \sum_(k < m.+1) (-1) ^+ k * qbin m k.

Lemma qalt_rec m : qalt m.+2 = (1 - q ^+ m.+1) * qalt m.
Proof.
rewrite /qalt big_ord_recl.
have E k : (-1) ^+ k.+1 * qbin m.+2 k.+1 =
    ((-1) ^+ k.+1 * qbin m.+1 k.+1 - (-1) ^+ k * qbin m.+1 k)
    + (1 - q ^+ m.+1) * ((-1) ^+ k * qbin m k).
  rewrite mulrCA -qbin_absorb qbinSS exprS mulN1r.
  move: (qbin m.+1 k) (qbin m.+1 k.+1) ((-1) ^+ k) (q ^+ k.+1).
  move=> b0 b1 s Q; rewrite mulrBl mul1r mulrBr !mulNr mulrDr opprD.
  by rewrite [- (s * b1) - _]addrC -addrA addKr.
rewrite (eq_bigr (fun i : 'I_m.+2 =>
    ((-1) ^+ i.+1 * qbin m.+1 i.+1 - (-1) ^+ i * qbin m.+1 i)
    + (1 - q ^+ m.+1) * ((-1) ^+ i * qbin m i))); last first.
  by move=> i _; exact: E.
rewrite big_split /= -mulr_sumr.
rewrite -(big_mkord xpredT (fun i =>
  (-1) ^+ i.+1 * qbin m.+1 i.+1 - (-1) ^+ i * qbin m.+1 i)).
rewrite telescope_sumr // (@qbin_small m.+1 m.+2) //.
rewrite /= mulr0 expr0 !mul1r.
rewrite (big_ord_recr m.+1) /= (@qbin_small m m.+1) // mulr0 addr0.
by rewrite sub0r addrA addrN add0r.
Qed.

Lemma qalt_even t : qalt t.*2 = \prod_(j < t) (1 - q ^+ j.*2.+1).
Proof.
elim: t => [|t IH]; first by rewrite big_ord0 /qalt big_ord1 /= mulr1.
by rewrite doubleS qalt_rec IH big_ord_recr /= mulrC.
Qed.

End QBin.

(* Gauss's evaluation of the q-binomials of the row n - 1 at a primitive    *)
(* n-th root of unity q (r is the inverse of q)                             *)
Lemma qbin_root (F : idomainType) (q r : F) n k : q * r = 1 ->
  n.-primitive_root q -> (k < n)%N ->
  qbin q n.-1 k = (-1) ^+ k * r ^+ 'C(k.+1, 2).
Proof.
move=> qr qp; elim: k => [|k IH] kn; first by rewrite qbinn0 mul1r.
have n0 : (0 < n)%N := prim_order_gt0 qp.
have qe : q ^+ (n.-1 - k) = r ^+ k.+1.
  rewrite -[LHS]mulr1 -(expr1n _ k.+1) -qr exprMn mulrA -exprD.
  have -> : (n.-1 - k + k.+1 = n)%N.
    by rewrite addnS subnK ?prednK // -ltnS prednK // ltnW.
  by rewrite (prim_expr_order qp) mul1r.
have E : 1 - q ^+ (n.-1 - k) = - r ^+ k.+1 * (1 - q ^+ k.+1).
  by rewrite qe mulrBr mulr1 mulNr opprK -exprMn mulrC qr expr1n addrC.
have q1 : 1 - q ^+ k.+1 != 0.
  by rewrite subr_eq0 eq_sym -(prim_order_dvd qp) gtnNdvd.
apply: (mulfI q1); rewrite -qbin_ratio E IH ?(ltn_trans (ltnSn k)) //.
rewrite -mulrA mulNr mulrCA -mulrN; congr (_ * _).
rewrite [(-1) ^+ k.+1]exprS mulN1r mulNr mulrCA -exprD.
by rewrite [in RHS]binS bin1 addnC.
Qed.

Lemma sum_shift_periodic (R : zmodType) (f : nat -> R) n h :
  (forall i, f (i + n)%N = f i) ->
  \sum_(i < n) f (i + h)%N = \sum_(i < n) f i.
Proof.
move=> fP; elim: h => [|h IH]; first by apply: eq_bigr => i _; rewrite addn0.
case: n fP IH => [|n] fP IH; first by rewrite !big_ord0.
pose g i := f (i + h)%N.
have A : \sum_(i < n.+2) g i = g 0%N + \sum_(i < n.+1) g i.+1.
  by rewrite big_ord_recl.
have B : \sum_(i < n.+2) g i = \sum_(i < n.+1) g i + g n.+1.
  by rewrite big_ord_recr.
have gn : g n.+1 = g 0%N by rewrite /g add0n addnC fP.
have -> : \sum_(i < n.+1) f (i + h.+1)%N = \sum_(i < n.+1) g i.+1.
  by apply: eq_bigr => i _; rewrite /g addnS addSn.
by rewrite -IH; apply: (addrI (g 0%N)); rewrite -A B gn addrC.
Qed.

Lemma bin2_double k : ('C(k.+1, 2) * 2 = k.+1 * k)%N.
Proof. by elim: k => [//|k IH]; rewrite binS bin1 mulnDl IH; nia. Qed.

Lemma prod_odd_expr (R : comNzRingType) (z : R) t :
  \prod_(j < t) z ^+ j.*2.+1 = z ^+ (t * t).
Proof.
elim: t => [|t IH]; first by rewrite big_ord0.
by rewrite big_ord_recr /= IH -exprD; congr (z ^+ _); rewrite -mul2n; nia.
Qed.

(* Gauss's product formula, for every odd n and primitive n-th root z *)
Lemma gauss_prod (F : fieldType) (z : F) n : odd n -> n.-primitive_root z ->
  \sum_(a < n) z ^+ (a * a) =
  \prod_(j < n./2) (z ^+ j.*2.+1 - z ^- j.*2.+1).
Proof.
move=> on zp; set m := n./2.
have hn : n = m.*2.+1 by rewrite -[n in LHS]odd_double_half on.
have n0 : (0 < n)%N by rewrite hn.
have zn := prim_expr_order zp.
have z0 : z != 0.
  by apply: contra_eq_neq zn => ->; rewrite expr0n gtn_eqF // eq_sym oner_neq0.
set r := z ^+ 2.
have rp : n.-primitive_root r by rewrite prim_root_exp_coprime // coprime2n.
set q := r ^+ n.-1.
have qp : n.-primitive_root q by rewrite prim_root_exp_coprime // coprimePn.
have qr : q * r = 1 by rewrite /q -exprSr prednK // (prim_expr_order rp).
have zq a : z ^+ a * q ^+ a = z ^- a.
  apply: (mulfI (expf_neq0 a z0)); rewrite divff ?expf_neq0 // mulrA -exprMn.
  by rewrite -expr2 -/r -exprMn mulrC qr expr1n.
have S : \sum_(a < n) z ^+ (a * a) = z ^+ (m.+1 * m.+1) * qalt q n.-1.
  rewrite /qalt prednK // mulr_sumr.
  rewrite -(@sum_shift_periodic _ (fun a => z ^+ (a * a)) n m.+1).
    apply: eq_bigr => k _; rewrite (qbin_root qr qp) ?ltn_ord //.
    rewrite [(-1) ^+ k * _]mulrA -exprMn mulrNN mulr1 expr1n mul1r.
    rewrite /r -exprM -exprD.
    have sq (i : nat) : ((i + m.+1) * (i + m.+1) =
        m.+1 * m.+1 + 2 * 'C(i.+1, 2) + n * i)%N.
      by rewrite mulnC bin2_double hn -mul2n; nia.
    by rewrite sq exprD exprM zn expr1n mulr1.
  move=> i; have -> : ((i + n) * (i + n) = i * i + n * (i.*2 + n))%N.
    by rewrite -mul2n; nia.
  by rewrite exprD [z ^+ (n * _)]exprM zn expr1n mulr1.
rewrite S hn /= -/m qalt_even.
rewrite [RHS](eq_bigr (fun j : 'I_m => z ^+ j.*2.+1 * (1 - q ^+ j.*2.+1))).
  rewrite big_split /= prod_odd_expr; congr (_ * _).
  have -> : (m.+1 * m.+1 = m * m + n)%N by rewrite hn -mul2n; nia.
  by rewrite exprD zn mulr1.
by move=> j _; rewrite mulrBr mulr1 zq.
Qed.

(* prod_(k = 1 .. n - 1) (1 - z ^ k) = n for z a primitive n-th root *)
Lemma prod_one_sub_root (F : fieldType) (z : F) n : n.-primitive_root z ->
  \prod_(k < n.-1) (1 - z ^+ k.+1) = n%:R.
Proof.
move=> zp; have n0 := prim_order_gt0 zp.
have E := factor_Xn_sub_1 zp.
rewrite subrX1 -(prednK n0) big_nat_recl // expr0 -/(polyC 1) in E.
have X1 : ('X - 1%:P : {poly F}) != 0 by rewrite polyXsubC_eq0.
move/(mulfI X1): E => /(congr1 (horner^~ 1)).
rewrite horner_prod horner_sum big_mkord.
rewrite (eq_bigr (fun i : 'I_n.-1 => 1 - z ^+ i.+1)); last first.
  by move=> i _; rewrite hornerXsubC.
under [X in _ = X -> _]eq_bigr do rewrite hornerXn expr1n.
by rewrite sumr_const card_ord prednK // => ->.
Qed.

Lemma prod_double_split (R : comNzRingType) (f : nat -> R) t :
  \prod_(k < t.*2) f k = \prod_(j < t) f j.*2 * \prod_(j < t) f j.*2.+1.
Proof.
elim: t => [|t IH]; first by rewrite !big_ord0 mulr1.
rewrite doubleS !big_ord_recr /= IH -!mulrA; congr (_ * _).
by rewrite mulrCA.
Qed.

Lemma prod_expr_succ (R : comNzRingType) (z : R) t :
  \prod_(k < t) z ^+ k.+1 = z ^+ 'C(t.+1, 2).
Proof.
elim: t => [|t IH]; first by rewrite big_ord0.
by rewrite big_ord_recr /= IH -exprD [in RHS]binS bin1.
Qed.

(* the square of Gauss's product *)
Lemma gauss_prod_sqr (F : fieldType) (z : F) n : odd n ->
  n.-primitive_root z ->
  (\prod_(j < n./2) (z ^+ j.*2.+1 - z ^- j.*2.+1)) ^+ 2 =
  (-1) ^+ n./2 * n%:R.
Proof.
move=> on zp; set m := n./2.
have hn : n = m.*2.+1 by rewrite -[n in LHS]odd_double_half on.
have n0 : (0 < n)%N by rewrite hn.
have zn := prim_expr_order zp.
have z0 : z != 0.
  by apply: contra_eq_neq zn => ->; rewrite expr0n gtn_eqF // eq_sym oner_neq0.
pose g a := z ^+ a - z ^- a.
have gN a : (a <= n)%N -> g (n - a)%N = - g a.
  move=> an; have e : z ^+ (n - a) = z ^- a.
    apply: (mulIf (expf_neq0 a z0)); rewrite -exprD subnK // zn mulVf //.
    exact: expf_neq0.
  by rewrite /g e invrK opprB.
have rp : n.-primitive_root (z ^+ 2).
  by rewrite prim_root_exp_coprime // coprime2n.
have A : \prod_(k < m.*2) g k.+1 = n%:R.
  rewrite (eq_bigr (fun k : 'I_m.*2 =>
    - (z ^+ k.+1)^-1 * (1 - z ^+ 2 ^+ k.+1))); last first.
    move=> k _; rewrite /g mulNr mulrBr mulr1 -exprM mulnC exprM expr2.
    by rewrite mulKf ?expf_neq0 // opprB.
  rewrite big_split /= prodrN card_ord -mul2n exprM sqrrN !expr1n mul1r.
  rewrite prodfV prod_expr_succ mul2n -hn bin2odd // -/m exprM zn expr1n.
  by rewrite invr1 mul1r -(prod_one_sub_root rp) hn.
have B : \prod_(j < m) g j.*2.+2 = (-1) ^+ m * \prod_(j < m) g j.*2.+1.
  have -> : \prod_(j < m) g j.*2.+2 = \prod_(j < m) - g j.*2.+1.
    rewrite [LHS](reindex_inj rev_ord_inj); apply: eq_bigr => j _ /=.
    have -> : ((m - j.+1).*2.+2 = n - j.*2.+1)%N.
      by rewrite hn; have := ltn_ord j; lia.
    by rewrite gN // hn; have := ltn_ord j; lia.
  by rewrite prodrN card_ord.
move: A; rewrite (prod_double_split (fun k => g k.+1)) /= B.
rewrite mulrCA -expr2 => <-.
by rewrite mulrA -exprD addnn -mul2n exprM sqrrN !expr1n mul1r.
Qed.

Section GaussC.

Variable C : numClosedFieldType.

Lemma subC_conj (x : C) : x - x^* = 'i * ('Im x *+ 2).
Proof.
rewrite ImE -mulr_natr divfK ?pnatr_eq0 // mulrA -expr2 sqrCi mulN1r.
by rewrite opprB.
Qed.

Lemma unit_invC (x : C) : `|x| = 1 -> x^-1 = x^*.
Proof. by move=> nx; rewrite invC_norm nx expr1n invr1 mul1r. Qed.

(* omega_n ^+ k is strictly in the upper half plane for 0 < k < n *)
Lemma Im_rootC_N1_expr_gt0 n k : (0 < k < n)%N ->
  0 < 'Im (n.-root (-1 : C) ^+ k).
Proof.
case/andP=> k0 kn; have n0 : (0 < n)%N := ltn_trans k0 kn.
set w := n.-root (-1 : C).
have wp : (2 * n).-primitive_root w := rootC_N1_prim C n0.
have [I _] := rootC_N1_sector C n0 (ltnW kn).
rewrite lt_def I andbT; apply/eqP => I0.
have nw : `|w ^+ k| = 1.
  by rewrite normrX (unity_norm _ (prim_expr_order wp)) ?expr1n // muln_gt0.
have [w1|wN1] := unit_real nw I0.
  have := prim_order_dvd wp k; rewrite w1 eqxx => /(dvdn_leq k0).
  by rewrite leqNgt (ltn_trans kn) // -{1}[n]mul1n ltn_pmul2r.
have : w ^+ (k * 2) == 1 by rewrite exprM wN1 sqrrN expr1n.
rewrite -(prim_order_dvd wp) [(k * 2)%N]mulnC dvdn_pmul2l //.
by move=> /(dvdn_leq k0); rewrite leqNgt kn.
Qed.

(* omega_n ^+ k is strictly in the lower half plane for n < k < 2 n *)
Lemma Im_rootC_N1_expr_lt0 n k : (n < k < n.*2)%N ->
  'Im (n.-root (-1 : C) ^+ k) < 0.
Proof.
case/andP=> nk kn; have n0 : (0 < n)%N by move: kn; rewrite -addnn; lia.
rewrite -(subnK (ltnW nk)) exprD rootCK // mulrN1 raddfN /= oppr_lt0.
by apply: Im_rootC_N1_expr_gt0; move: nk kn; rewrite -addnn; lia.
Qed.

(* zeta_n = omega_n ^+ 2 = e^(2 i pi / n) and the quadratic Gauss sum *)
Definition gauss_zeta n : C := n.-root (-1) ^+ 2.

Definition gauss_sum n : C := \sum_(a < n) gauss_zeta n ^+ (a * a).

Lemma gauss_zeta_prim n : (0 < n)%N -> n.-primitive_root (gauss_zeta n).
Proof.
move=> n0; have := exp_prim_root (rootC_N1_prim C n0) 2.
by rewrite gcdnMr mulKn.
Qed.

(* Gauss's theorem, for every odd n *)
Theorem gauss_sumC n : odd n -> gauss_sum n = 'i ^+ odd n./2 * sqrtC n%:R.
Proof.
move=> on; set m := n./2.
have hn : n = m.*2.+1 by rewrite -[n in LHS]odd_double_half on.
have n0 : (0 < n)%N by rewrite hn.
set w := n.-root (-1 : C).
have wp : (2 * n).-primitive_root w := rootC_N1_prim C n0.
have nw k : `|w ^+ k| = 1.
  by rewrite normrX (unity_norm _ (prim_expr_order wp)) ?expr1n // muln_gt0.
have zp := gauss_zeta_prim n0.
have P2 := gauss_prod_sqr on zp.
rewrite /gauss_sum (gauss_prod on zp) in P2 *.
(* each factor is 'i times the real number y j *)
pose y j := 'Im (w ^+ (2 * j.*2.+1)) *+ 2.
have Fy j : gauss_zeta n ^+ j.*2.+1 - gauss_zeta n ^- j.*2.+1 = 'i * y j.
  by rewrite /gauss_zeta -exprM (unit_invC (nw _)) subC_conj.
rewrite (eq_bigr (fun j : 'I_m => 'i * y j)) in P2 *; last first.
  by move=> j _; exact: Fy.
rewrite big_split /= prodr_const card_ord in P2 *.
(* y j > 0 exactly for j < u, so that the product has sign (-1)^(m/2) *)
set u := uphalf m.
have hu : u = (odd m + m./2)%N := uphalf_half m.
have hmo := odd_double_half m.
have hm : m = (u + m./2)%N by rewrite hu; move: hmo; rewrite -addnn; lia.
pose s j : C := if (j < u)%N then 1 else -1.
pose a j := s j * y j.
have S : \prod_(i < m) s i = (-1) ^+ m./2.
  have um : (u <= m)%N by rewrite [X in (_ <= X)%N]hm leq_addr.
  rewrite -(big_mkord xpredT s) (big_cat_nat (leq0n u) um) /=.
  rewrite big_nat_cond big1 ?mul1r; last first.
    by move=> i /andP[/andP[_ iu] _]; rewrite /s iu.
  rewrite big_nat_cond (eq_bigr (fun _ => -1)); last first.
    by move=> i /andP[/andP[iu _] _]; rewrite /s ltnNge iu.
  by rewrite -big_nat_cond prodr_const_nat [X in (X - u)%N]hm addKn.
have Hlt (j : nat) : (j < u)%N -> (0 < 2 * j.*2.+1 < n)%N.
  move: hu hmo hn; rewrite -!addnn.
  by case: (odd m) => /= hu' hmo' hn' ju; rewrite hn'; lia.
have Hgt (j : nat) : (u <= j)%N -> (j < m)%N -> (n < 2 * j.*2.+1 < n.*2)%N.
  move: hu hmo hn; rewrite -!addnn.
  by case: (odd m) => /= hu' hmo' hn' ju jm; rewrite hn'; lia.
have Za : 0 < \prod_(i < m) a i.
  apply: prodr_gt0 => i _; rewrite /a /s; case: ifP => iu.
    rewrite mul1r pmulrn_lgt0 //; apply: Im_rootC_N1_expr_gt0.
    exact: Hlt.
  rewrite mulN1r oppr_gt0 pmulrn_llt0 //; apply: Im_rootC_N1_expr_lt0.
  by apply: Hgt (ltn_ord i); rewrite leqNgt iu.
have Ya : \prod_(i < m) y i = (-1) ^+ m./2 * \prod_(i < m) a i.
  rewrite /a big_split /= S mulrA -exprD addnn -mul2n exprM sqrrN !expr1n.
  by rewrite mul1r.
set Z := \prod_(i < m) a i in Za Ya.
have im : 'i ^+ m = 'i ^+ odd m * (-1) ^+ m./2 :> C.
  by rewrite -{1}hmo exprD -mul2n exprM sqrCi.
rewrite Ya im in P2 *.
have e : (-1) ^+ m./2 * ((-1) ^+ m./2 * Z) = Z.
  by rewrite mulrA -exprD addnn -mul2n exprM sqrrN !expr1n mul1r.
rewrite -mulrA e in P2 *.
(* the modulus: Z ^ 2 = n *)
have Z2 : Z ^+ 2 = n%:R.
  have sm : (-1) ^+ n./2 = (-1) ^+ odd m :> C.
    rewrite -[n./2]/m -[in LHS]hmo exprD -mul2n exprM sqrrN !expr1n.
    by rewrite mulr1.
  move: P2; rewrite sm exprMn -exprM mulnC exprM sqrCi => /mulfI; apply.
  by rewrite signr_eq0.
by rewrite -Z2 sqrCK // ltW.
Qed.

Lemma gauss_sum_sqr n : odd n -> gauss_sum n ^+ 2 = (-1) ^+ n./2 * n%:R.
Proof.
move=> on; have n0 : (0 < n)%N by case: n on.
rewrite /gauss_sum (gauss_prod on (gauss_zeta_prim n0)).
by rewrite gauss_prod_sqr // gauss_zeta_prim.
Qed.

Lemma odd_half_mod4 n : odd n -> odd n./2 = (n %% 4 == 3)%N.
Proof.
move=> on; rewrite -[n in RHS](odd_double_half n) on.
rewrite -[n./2 in RHS](odd_double_half n./2).
case: (odd n./2) => /=; set k := n./2./2.
  have -> : (1 + (1 + k.*2).*2 = k * 4 + 3)%N by lia.
  by rewrite modnMDl.
have -> : (1 + (0 + k.*2).*2 = k * 4 + 1)%N by lia.
by rewrite modnMDl.
Qed.

Theorem gauss_sum_1mod4 n : (n %% 4 = 1)%N -> gauss_sum n = sqrtC n%:R.
Proof.
move=> n4; have on : odd n.
  by rewrite [n in odd n](divn_eq n 4) n4 oddD oddM andbF.
by rewrite gauss_sumC // odd_half_mod4 // n4 expr0 mul1r.
Qed.

Theorem gauss_sum_3mod4 n : (n %% 4 = 3)%N -> gauss_sum n = 'i * sqrtC n%:R.
Proof.
move=> n4; have on : odd n.
  by rewrite [n in odd n](divn_eq n 4) n4 oddD oddM andbF.
by rewrite gauss_sumC // odd_half_mod4 // n4 expr1.
Qed.

(* the statement for an odd prime p *)
Theorem gauss_sum_prime p : prime p -> odd p ->
  gauss_sum p = if (p %% 4 == 1)%N then sqrtC p%:R else 'i * sqrtC p%:R.
Proof.
move=> _ op; rewrite gauss_sumC // odd_half_mod4 //.
have : (p %% 4 < 4)%N by rewrite ltn_mod.
have : odd (p %% 4).
  by move: op; rewrite [p in odd p](divn_eq p 4) oddD oddM andbF.
by case: (p %% 4)%N => [|[|[|[|]]]] //= _ _; rewrite ?expr0 ?mul1r ?expr1.
Qed.

(* sqrtC n as a sum of powers of a principal root of -1, exponents reduced *)
Lemma gauss_sum_rootE n : (0 < n)%N ->
  gauss_sum n = \sum_(a < n) n.-root (-1 : C) ^+ ((a * a).*2 %% n.*2).
Proof.
move=> n0; apply: eq_bigr => a _.
rewrite expr_mod -?mul2n ?(prim_expr_order (rootC_N1_prim C n0)) //.
by rewrite /gauss_zeta -exprM.
Qed.

Lemma sqrtC_gauss_1mod4 n : (n %% 4 = 1)%N ->
  sqrtC n%:R = \sum_(a < n) n.-root (-1 : C) ^+ ((a * a).*2 %% n.*2).
Proof.
move=> n4; have n0 : (0 < n)%N by case: n n4.
by rewrite -gauss_sum_rootE // gauss_sum_1mod4.
Qed.

(* 'i = omega_2n ^+ n and omega_n = omega_2n ^+ 2 (index law) *)
Lemma sqrtC_gauss_3mod4 n : (n %% 4 = 3)%N ->
  sqrtC n%:R =
  \sum_(a < n) (n.*2).-root (-1 : C) ^+ ((n * 3 + a * a * 4) %% (n * 4)).
Proof.
move=> n4; have n0 : (0 < n)%N by case: n n4.
set psi := (n.*2).-root (-1 : C).
have psiN : psi ^+ n.*2 = -1 by rewrite rootCK // double_gt0.
have psi4 : psi ^+ (n * 4) = 1.
  have -> : (n * 4 = n.*2 * 2)%N by rewrite -muln2; lia.
  by rewrite exprM psiN sqrrN expr1n.
have psii : psi ^+ n = 'i by rewrite /psi -mul2n rootC_N1_index // omega2C.
have psiw : psi ^+ 2 = n.-root (-1) by rewrite /psi -muln2 rootC_N1_index.
have E a : psi ^+ ((n * 3 + a * a * 4) %% (n * 4)) =
    - 'i * gauss_zeta n ^+ (a * a).
  rewrite expr_mod // /gauss_zeta -psiw -!exprM.
  have -> : (n * 3 + a * a * 4 = n.*2 + n + 2 * (2 * (a * a)))%N.
    by rewrite -addnn; lia.
  by rewrite !exprD psiN psii mulN1r.
rewrite (eq_bigr (fun a : 'I_n => - 'i * gauss_zeta n ^+ (a * a))).
  rewrite -mulr_sumr -/(gauss_sum n).
  by rewrite gauss_sum_3mod4 // mulrA mulNr -expr2 sqrCi opprK mul1r.
by move=> a _; exact: E.
Qed.

(* non-vacuity: the first odd primes *)
Example gauss_sum3 : gauss_sum 3 = 'i * sqrtC 3%:R.
Proof. exact: gauss_sum_3mod4. Qed.

Example gauss_sum5 : gauss_sum 5 = sqrtC 5%:R.
Proof. exact: gauss_sum_1mod4. Qed.

Example gauss_sum7 : gauss_sum 7 = 'i * sqrtC 7%:R.
Proof. exact: gauss_sum_3mod4. Qed.

Example sqrtC7_root : sqrtC 7%:R =
  \sum_(a < 7) 14.-root (-1 : C) ^+ ((7 * 3 + a * a * 4) %% (7 * 4)).
Proof. exact: sqrtC_gauss_3mod4. Qed.

End GaussC.
