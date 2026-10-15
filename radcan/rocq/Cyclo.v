(******************************************************************************)
(* Cyclo: cyclotomic reduction of the roots of unity (milestone Omega5).      *)
(* omega_n = proot r n (-1) is a primitive 2n-th root of unity on C, so every *)
(* polynomial in the omega atoms is reduced modulo Phi_2N, N the lcm of the   *)
(* indices, after rewriting omega_n as omega_N ^+ (N / n).                    *)
(*   zadd, zmul, zxm1, zprod == integer polynomials (seq Z, degree 0 first),  *)
(*                  X ^ m - 1, prod_(d <- D) (X ^ d - 1)                      *)
(*   zhorner x a == the value of a at x in a numFieldType                     *)
(*   prim_root_cert(_val) : p * h = X ^ m - 1, h * g = prod_(d <- D)          *)
(*                  (X ^ d - 1), 0 < d < m for d in D, z a primitive m-th     *)
(*                  root of unity: p (z) = 0                                  *)
(*   cyclo m     == Phi_m by the Moebius product (unverified)                 *)
(*   cyc_cert m  == Some (cyclo m) when its certificate checks                *)
(*   ctab phi r k == the remainders of r * X ^ j modulo phi, j < k            *)
(*   cyc_nf N tbl p == the normal form p with every omega_n ^+ k rewritten as *)
(*                  the remainder of X ^ (k N / n) at omega_N (table tbl)     *)
(*   cyc_eqb p1 p2 == both forms agree after cyc_nf (N common to p1, p2)      *)
(*   radcan_check_cyc e1 e2 == radcan_check_negc, then the normal forms of    *)
(*                  modes MNegC, MNegCW compared by cyc_eqb                   *)
(*   wprim r     == proot r n (-1) is a primitive 2n-th root of unity         *)
(*   cycprim w   == the same on wroot w n (record, instance on C in           *)
(*                  CycloC.v)                                                 *)
(*   radcan_eq_cond_cyc, radcan_eq_refined_cyc == the decision theorems,      *)
(*                  given w : negroot r, cycroot w and cycprim w              *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts Syntax Radcan Refine.
From Radcan Require Import RealRoot OmegaRoot2.
Import Order.TTheory GRing.Theory Num.Theory ZNum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Integer polynomials, coefficient of degree 0 first *)

Fixpoint zadd (a b : seq Z) : seq Z :=
  match a, b with
  | [::], _ => b
  | _, [::] => a
  | x :: a', y :: b' => Z.add x y :: zadd a' b'
  end.

Definition zscale (c : Z) (a : seq Z) : seq Z := map (Z.mul c) a.
Definition zopp (a : seq Z) : seq Z := map Z.opp a.
Definition zsub (a b : seq Z) : seq Z := zadd a (zopp b).

Definition zmul (a b : seq Z) : seq Z :=
  foldr (fun c acc => zadd (zscale c b) (Z0 :: acc)) [::] a.

Definition zeqb (a b : seq Z) : bool := all (Z.eqb 0) (zsub a b).

(* X ^ k * a, X ^ m - 1, prod_(d <- ds) (X ^ d - 1) *)
Definition zshift (k : nat) (a : seq Z) : seq Z := nseq k Z0 ++ a.
Definition zxm1 (m : nat) : seq Z := zadd (zshift m [:: Zpos 1]) [:: Zneg 1].
Definition zprod (ds : seq nat) : seq Z :=
  foldr (fun d acc => zmul (zxm1 d) acc) [:: Zpos 1] ds.

(* trailing zeros removed *)
Definition zstrip (a : seq Z) : seq Z :=
  foldr (fun c acc => if nilp acc && Z.eqb c 0 then [::] else c :: acc)
    [::] a.

(* Unverified computations: quotient by a monic b, Phi_m, its certificate *)

Fixpoint zdivf (f : nat) (a b : seq Z) : seq Z :=
  if f is f'.+1 then
    let a := zstrip a in
    if (size a < size b)%N then [::] else
    let c := last Z0 a in let k := (size a - size b)%N in
    zadd (zshift k [:: c]) (zdivf f' (zsub a (zshift k (zscale c b))) b)
  else [::].

Definition zdiv (a b : seq Z) : seq Z := zdivf (size a).+1 a (zstrip b).

(* the squarefree divisors d of the product of ps, with the parity of the
   number of primes of d *)
Definition msubsets (ps : seq nat) : seq (nat * bool) :=
  foldr (fun p acc => acc ++ map (fun db => (db.1 * p, ~~ db.2)%N) acc)
    [:: (1%N, false)] ps.

(* Phi_m = prod_(d | m) (X ^ (m / d) - 1) ^ mu(d) *)
Definition cyclo (m : nat) : seq Z :=
  let s := msubsets (primes m) in
  let num := zprod [seq (m %/ db.1)%N | db <- s & ~~ db.2] in
  let den := zprod [seq (m %/ db.1)%N | db <- s & db.2] in
  zstrip (zdiv num den).

(* p * h = X ^ m - 1, h * g = prod_(q prime | m) (X ^ (m / q) - 1) *)
Definition cyc_cert (m : nat) : option (seq Z) :=
  let p := cyclo m in
  let h := zdiv (zxm1 m) p in
  let D := [seq (m %/ q)%N | q <- primes m] in
  let G := zprod D in
  let g := zdiv G h in
  if [&& zeqb (zmul p h) (zxm1 m), zeqb (zmul h g) G
       & all (fun d => 0 < d < m)%N D] then Some p else None.

(* r * X reduced by phi (when its degree reaches the one of phi) *)
Definition xstep (phi r : seq Z) : seq Z :=
  let r' := Z0 :: r in
  if (size r' < size phi)%N then r'
  else zstrip (zsub r' (zscale (last Z0 r') phi)).

Fixpoint ctab (phi r : seq Z) (k : nat) : seq (seq Z) :=
  if k is k'.+1 then r :: ctab phi (xstep phi r) k' else [::].

Local Open Scope ring_scope.

Section ZHorner.

Variables (F : numFieldType) (x : F).

Definition zhorner (a : seq Z) : F :=
  foldr (fun c acc => Z2F F c + x * acc) 0 a.

Lemma zhorner_add a b : zhorner (zadd a b) = zhorner a + zhorner b.
Proof.
elim: a b => [|c a IH] [|d b] /=; rewrite ?add0r ?addr0 //.
by rewrite Z2F_add IH mulrDr addrACA.
Qed.

Lemma zhorner_scale c a : zhorner (zscale c a) = Z2F F c * zhorner a.
Proof.
elim: a => [|d a IH] /=; first by rewrite mulr0.
by rewrite Z2F_mul IH mulrDr mulrCA.
Qed.

Lemma zhorner_opp a : zhorner (zopp a) = - zhorner a.
Proof.
by elim: a => [|d a IH] /=; rewrite ?oppr0 // Z2F_opp IH mulrN opprD.
Qed.

Lemma zhorner_sub a b : zhorner (zsub a b) = zhorner a - zhorner b.
Proof. by rewrite zhorner_add zhorner_opp. Qed.

Lemma zhorner_mul a b : zhorner (zmul a b) = zhorner a * zhorner b.
Proof.
elim: a => [|c a IH] /=; first by rewrite mul0r.
by rewrite zhorner_add zhorner_scale /= add0r IH mulrDl mulrA.
Qed.

Lemma zhorner_eq0 a : all (Z.eqb 0) a -> zhorner a = 0.
Proof.
elim: a => [|c a IH] //= /andP[]; case: c => // _ /IH ->.
by rewrite mulr0 addr0.
Qed.

Lemma zeqbP a b : zeqb a b -> zhorner a = zhorner b.
Proof.
by move/zhorner_eq0; rewrite zhorner_sub => /eqP; rewrite subr_eq0 => /eqP.
Qed.

Lemma zhorner_shift k a : zhorner (zshift k a) = x ^+ k * zhorner a.
Proof.
elim: k => [|k IH] /=; first by rewrite mul1r.
by rewrite add0r IH exprS mulrA.
Qed.

Lemma zhorner_xm1 m : zhorner (zxm1 m) = x ^+ m - 1.
Proof.
by rewrite zhorner_add zhorner_shift /= pos2F1 mulr0 !addr0 mulr1.
Qed.

Lemma zhorner_prod ds :
  zhorner (zprod ds) = \prod_(d <- ds) (x ^+ d - 1).
Proof.
elim: ds => [|d ds IH] /=; first by rewrite big_nil pos2F1 mulr0 addr0.
by rewrite zhorner_mul zhorner_xm1 IH big_cons.
Qed.

Lemma zhorner_strip a : zhorner (zstrip a) = zhorner a.
Proof.
elim: a => [|c a IH] //=; case: ifP => [/andP[/nilP E] |_ /=]; last first.
  by rewrite IH.
by case: c => // _; rewrite -IH E /= mulr0 addr0.
Qed.

End ZHorner.

(* The certificate lemma *)

Lemma prim_root_cert_val (R : idomainType) m (z P H G : R) (D : seq nat) :
  m.-primitive_root z -> all (fun d => 0 < d < m)%N D ->
  P * H = z ^+ m - 1 -> H * G = \prod_(d <- D) (z ^+ d - 1) -> P = 0.
Proof.
move=> zp HD PH HG.
have H0 : H != 0.
  apply/eqP => H0; move: HG; rewrite H0 mul0r => /esym/eqP; apply/negP.
  rewrite prodf_seq_neq0; apply/allP => d /(allP HD) /andP[d0 dm] /=.
  rewrite subr_eq0; apply/negP; rewrite -(prim_order_dvd zp) => /dvdn_leq.
  by rewrite d0 leqNgt dm => /(_ isT).
move: PH; rewrite (prim_expr_order zp) subrr => /eqP.
by rewrite mulf_eq0 (negbTE H0) orbF => /eqP.
Qed.

Lemma prim_root_cert (R : idomainType) m (z : R) (p h g : {poly R})
    (D : seq nat) :
  m.-primitive_root z -> all (fun d => 0 < d < m)%N D ->
  p * h = 'X^m - 1 -> h * g = \prod_(d <- D) ('X^d - 1) -> root p z.
Proof.
move=> zp HD /(congr1 (horner^~ z)) PH /(congr1 (horner^~ z)) HG.
apply/rootP; apply: (prim_root_cert_val zp HD (H := h.[z]) (G := g.[z])).
  by rewrite -hornerM PH hornerD hornerN hornerXn hornerC.
rewrite -hornerM HG horner_prod; apply: eq_bigr => d _.
by rewrite hornerD hornerN hornerXn hornerC.
Qed.

Section CycCert.

Variables (F : numFieldType) (m : nat) (z : F).
Hypothesis zp : m.-primitive_root z.

Lemma cyc_certP phi : cyc_cert m = Some phi -> zhorner z phi = 0.
Proof.
rewrite /cyc_cert; case: ifP => // /and3P[E1 E2 HD] [<-].
move/(zeqbP z): E1; rewrite zhorner_mul zhorner_xm1 => E1.
move/(zeqbP z): E2; rewrite zhorner_mul zhorner_prod => E2.
exact: prim_root_cert_val zp HD E1 E2.
Qed.

Variable phi : seq Z.
Hypothesis phi0 : zhorner z phi = 0.

Lemma xstepE a : zhorner z (xstep phi a) = z * zhorner z a.
Proof.
rewrite /xstep; case: ifP => _ /=; first by rewrite add0r.
by rewrite zhorner_strip zhorner_sub zhorner_scale phi0 mulr0 subr0 /= add0r.
Qed.

Lemma ctabE a k j : (j < k)%N ->
  zhorner z (nth [::] (ctab phi a k) j) = zhorner z a * z ^+ j.
Proof.
elim: k a j => [|k IH] a [|j] //= jk; first by rewrite mulr1.
by rewrite IH // xstepE exprS mulrCA mulrA.
Qed.

End CycCert.

(* The pass on normal forms *)

(* the indices of the omega atoms of p *)
Definition omega_idx (p : nf) : seq nat :=
  flatten [seq [seq Pos.to_nat nk.1 | nk <- (vsplit_omega t.2.1).1] | t <- p].

(* c * v * a ^+ k * R (a), as a normal form with key part m *)
Fixpoint zterms (c : coef) (v : vmono) (m : mono) (a : atom) (R : seq Z)
    (k : nat) : nf :=
  if R is z :: R' then
    nf_add (nf_single (c_mul c (c_of_Z z)) (vmono_mul v (vsingle a k), m))
           (zterms c v m a R' k.+1)
  else [::].

(* the omega part of a term is omega_N ^+ j, written by its remainder *)
Definition cyc_term (N : positive) (tbl : seq (seq Z)) (t : coef * key) : nf :=
  let: (o, v) := vsplit_omega t.2.1 in
  let n := Pos.to_nat N in
  if all (fun nk => Pos.to_nat nk.1 %| n)%N o then
    let j := foldr (fun nk acc => nk.2 * (n %/ Pos.to_nat nk.1) + acc)%N
                   0%N o in
    zterms t.1 v t.2.2 (ARoot N omega_c) (nth [::] tbl (j %% (2 * n))) 0
  else [:: t].

Definition cyc_nf (N : positive) (tbl : seq (seq Z)) (p : nf) : nf :=
  foldr (fun t acc => nf_add (cyc_term N tbl t) acc) [::] p.

Definition cyc_eqb (p1 p2 : nf) : bool :=
  let N := Pos.of_nat (foldr lcmn 1%N (omega_idx p1 ++ omega_idx p2)) in
  let m := (2 * Pos.to_nat N)%N in
  if cyc_cert m is Some phi then
    let tbl := ctab phi [:: Zpos 1] m in
    nf_eqb (cyc_nf N tbl p1) (cyc_nf N tbl p2)
  else false.

Arguments cyc_eqb : simpl never.

(* The checkers: modes MNegC, MNegCW, compared through cyc_eqb *)

Definition radcan_check_cyc_bs (rt : bool) (m : rmode) (hs bs : seq nf)
  (e1 e2 : rexpr) : option (seq cond) :=
  let: (p1, p2, cs) := radcan_nfb rt m hs bs e1 e2 in
  if cyc_eqb p1 p2 then Some cs else None.

Definition radcan_check_cyc_m (m : rmode) (e1 e2 : rexpr) :
    option (seq cond) :=
  let cb := const_basis (rconsts m e1 ++ rconsts m e2) in
  let f1 := cb_rw m cb e1 in let f2 := cb_rw m cb e2 in
  let hs := neg_hints [:: f1; f2] in
  let ck rt := radcan_check_cyc_bs rt m hs (mk_basis_n rt m hs [:: f1; f2])
                 f1 f2 in
  if ck false is Some cs then Some cs else ck true.

Definition radcan_check_cyc (e1 e2 : rexpr) : option (seq cond) :=
  if radcan_check_negc e1 e2 is Some cs then Some cs
  else if radcan_check_cyc_m MNegC e1 e2 is Some cs then Some cs
  else radcan_check_cyc_m MNegCW e1 e2.

(* Soundness *)

Definition wprim (F : numFieldType) (r : posroot F) : Prop :=
  forall n, (0 < n)%N -> (2 * n).-primitive_root (proot r n (-1)).

Record cycprim (F : numFieldType) (r : posroot F) (w : negroot r) : Prop :=
  CycPrim {
  wroot_prim : forall n, (0 < n)%N -> (2 * n).-primitive_root (wroot w n)
}.

Lemma cycprim_wprim (F : numFieldType) (r : posroot F) (w : negroot r) :
  cycprim w -> wprim r.
Proof. by move=> [cp] n n0; rewrite -(wrootE w n0); exact: cp. Qed.

Lemma cyc_pos_gt0 (n : positive) : (0 < Pos.to_nat n)%N.
Proof. by apply/ssrnat.ltP/Pos2Nat.is_pos. Qed.

Section CycSound.

Variables (F : numFieldType) (r : posroot F) (env : seq F).
Hypotheses (hw : windex r) (hp : wprim r).

Local Notation nf_interp := (nf_interp r env).
Local Notation vmono_interp := (vmono_interp r env).
Local Notation key_interp := (key_interp r env).
Local Notation om n := (proot r n (-1)).

Local Arguments nf_add : simpl never.

Lemma omega_atomE N :
  atom_interp r env (ARoot N omega_c) = om (Pos.to_nat N).
Proof. by rewrite /= pos2F1. Qed.

Lemma zterms_sound c v m a R k :
  nf_interp (zterms c v m a R k) = C2F c * vmono_interp v * mono_interp r m
    * atom_interp r env a ^+ k * zhorner (atom_interp r env a) R.
Proof.
elim: R k => [|z R IH] k /=; first by rewrite nf_interp_nil mulr0.
rewrite nf_add_sound nf_single_sound IH /key_interp /=.
rewrite vmono_mul_sound vsingle_sound C2F_c_mul C2F_c_of_Z exprS.
move: (C2F c) (Z2F F z) (vmono_interp v) (atom_interp r env a)
  (mono_interp r m) (zhorner _ R) => C Z V A M H.
rewrite mulrDr; congr (_ + _).
  rewrite -!mulrA; congr (_ * _); rewrite mulrCA; congr (_ * _).
  by rewrite mulrCA [RHS]mulrCA [Z * M]mulrC.
by rewrite -!mulrA; do 3 congr (_ * _); rewrite mulrCA.
Qed.

Lemma omega_prod_lift n (o : seq (positive * nat)) : (0 < n)%N ->
  all (fun nk => Pos.to_nat nk.1 %| n)%N o ->
  \prod_(nk <- o) om (Pos.to_nat nk.1) ^+ nk.2 =
  om n ^+ foldr (fun nk acc => nk.2 * (n %/ Pos.to_nat nk.1) + acc)%N 0%N o.
Proof.
move=> n0; elim: o => [|[a k] o IH] /=; first by rewrite big_nil.
case/andP => an /IH {}IH; rewrite big_cons IH exprD /=.
by rewrite (windex_lift hw k _ n0 an) // cyc_pos_gt0.
Qed.

Lemma cyc_term_sound N phi t :
  zhorner (om (Pos.to_nat N)) phi = 0 ->
  nf_interp (cyc_term N (ctab phi [:: Zpos 1] (2 * Pos.to_nat N)) t) =
  C2F t.1 * key_interp t.2.
Proof.
move=> phi0; rewrite /cyc_term; have := vsplit_omega_sound r env t.2.1.
case: (vsplit_omega _) => o v /= Hv.
case: ifP => [Ho|_]; last by rewrite nf_interp_cons nf_interp_nil addr0.
have n0 := cyc_pos_gt0 N.
have m0 : (0 < 2 * Pos.to_nat N)%N by rewrite muln_gt0.
rewrite zterms_sound omega_atomE expr0 mulr1 (ctabE phi0) ?ltn_pmod //.
rewrite /= pos2F1 mulr0 addr0 mul1r /key_interp Hv (omega_prod_lift n0 Ho).
set j := foldr _ _ _.
rewrite [in RHS](divn_eq j (2 * Pos.to_nat N)) exprD.
rewrite [(_ %/ _ * _)%N]mulnC exprM (prim_expr_order (hp n0)) expr1n mul1r.
by rewrite -!mulrA [_ ^+ _ * mono_interp _ _]mulrC.
Qed.

Lemma cyc_nf_sound N phi p :
  zhorner (om (Pos.to_nat N)) phi = 0 ->
  nf_interp (cyc_nf N (ctab phi [:: Zpos 1] (2 * Pos.to_nat N)) p) =
  nf_interp p.
Proof.
move=> phi0; elim: p => [|t p IH] //=.
by rewrite nf_add_sound IH cyc_term_sound // nf_interp_cons.
Qed.

Lemma cyc_eqb_sound p1 p2 : cyc_eqb p1 p2 -> nf_interp p1 = nf_interp p2.
Proof.
rewrite /cyc_eqb; set N := Pos.of_nat _.
case E : (cyc_cert _) => [phi|] // /(nf_eqb_eq r env).
have phi0 := cyc_certP (hp (cyc_pos_gt0 N)) E.
by rewrite (cyc_nf_sound p1 phi0) (cyc_nf_sound p2 phi0).
Qed.

(* the checkers in a neg mode m with the index law *)
Variable m : rmode.
Hypotheses (Hng : neg_mode m -> negroot r) (Hcy : cyc_mode m -> windex r).
Hypothesis Ho : odd_mode m -> oddroot r.
Hypothesis Hrl : real_mode m -> realroot r.

Lemma radcan_check_cyc_bs_sound rt hs bs e1 e2 cs :
  radcan_check_cyc_bs rt m hs bs e1 e2 = Some cs ->
  all_conds r env cs -> rinterp r env e1 = rinterp r env e2.
Proof.
have H1 := @normcr_sound F r env m Ho Hng Hrl Hcy rt hs bs e1.
have H2 := @normcr_sound F r env m Ho Hng Hrl Hcy rt hs bs e2.
set n1 := normcr rt m hs bs e1 in H1 *; set n2 := normcr rt m hs bs e2 in H2 *.
have E : radcan_check_cyc_bs rt m hs bs e1 e2 =
    if cyc_eqb n1.1 n2.1 then Some (cfilter m (cdedup (n1.2 ++ n2.2)))
    else None.
  clear H1 H2; rewrite /radcan_check_cyc_bs /radcan_nfb -/n1 -/n2.
  by case: n1; case: n2.
rewrite E; case: ifP => // /cyc_eqb_sound Hp [<-].
move=> /all_condsP /(cfilter_sound Hrl) /holds_dedup /holds_cat.
by case=> /H1 -> /H2 ->.
Qed.

Lemma radcan_check_cyc_m_sound e1 e2 cs :
  radcan_check_cyc_m m e1 e2 = Some cs ->
  all_conds r env cs -> rinterp r env e1 = rinterp r env e2.
Proof.
rewrite /radcan_check_cyc_m; set cb := const_basis _.
rewrite -(cb_rw_sound env Ho Hng cb e1) -(cb_rw_sound env Ho Hng cb e2).
by case/ocase_some => /radcan_check_cyc_bs_sound.
Qed.

End CycSound.

(* The decision theorems *)

Theorem radcan_eq_cond_cyc (F : numFieldType) (r : posroot F)
    (w : negroot r) (cy : cycroot w) (cp : cycprim w) (env : seq F)
    e1 e2 cs :
  radcan_check_cyc e1 e2 = Some cs -> all_conds r env cs ->
  rinterp r env e1 = rinterp r env e2.
Proof.
have hw := cycroot_windex cy; have hp := cycprim_wprim cp.
rewrite /radcan_check_cyc; case/ocase_some => H.
  exact: (radcan_eq_cond_negc cy H).
by case/ocase_some: H => H; apply: (radcan_check_cyc_m_sound hw hp _ _ _ _ H).
Qed.

Theorem radcan_eq_cyc (F : numFieldType) (r : posroot F) (w : negroot r)
    (cy : cycroot w) (cp : cycprim w) (env : seq F) e1 e2 :
  radcan_check_cyc e1 e2 = Some [::] -> rinterp r env e1 = rinterp r env e2.
Proof. by move/(radcan_eq_cond_cyc cy cp); apply. Qed.

Theorem radcan_eq_refined_cyc (F : numFieldType) (r : posroot F)
    (w : negroot r) (cy : cycroot w) (cp : cycprim w) (env : seq F)
    e1 e2 cs rcs :
  radcan_check_cyc e1 e2 = Some cs -> refine cs = rcs ->
  all_rconds F (proot r) env rcs -> rinterp r env e1 = rinterp r env e2.
Proof.
move=> H Hr Hc; apply: (radcan_eq_cond_cyc cy cp H).
by apply: all_conds_bridge_back; apply: refine_sound; rewrite Hr.
Qed.
