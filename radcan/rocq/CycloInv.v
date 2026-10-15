(******************************************************************************)
(* CycloInv: inverses of sums of roots of unity (cyclotomic inversion).       *)
(* An inverse atom AInv e of a normal form, e a polynomial q in the omega     *)
(* atoms (omega_n = proot r n (-1)), is replaced by a polynomial before the   *)
(* cyclotomic reduction of Cyclo.v; N is the lcm of the omega indices of q.   *)
(*   mulr1_neq0, mulr1_inv == u * v = 1 -> u != 0, u * v = 1 -> u^-1 = v     *)
(*   omega_only q    == every variable atom of q is an omega atom             *)
(*   key_coef k p    == the coefficient of the key k in p                     *)
(*   cyc_inv_cand q  == the candidate inverse of q (unverified), by Gauss-    *)
(*                      Jordan elimination over Q on the basis                *)
(*                      omega_N ^+ j * b, j < deg Phi_2N, b a root monomial   *)
(*                      of the bases of q (nf_basis), dimension <= 96         *)
(*   cyc_inv_exact q == Some v, q omega-only (rationals, omegas, constant     *)
(*                      real radicals), v = cyc_inv_cand q and q * v reduces  *)
(*                      to 1 modulo Phi_2N (cyc_eqb): q^-1 = v, no condition  *)
(*   cyc_conj N a q  == q with omega_N ^+ j -> omega_N ^+ (a j) (unverified)  *)
(*   cyc_norm_cof q  == (P, n): P the product of the conjugates of q, a prime *)
(*                      to 2N, 1 < a < 2N, n = q * P reduced (the norm)       *)
(*   cyc_inv_norm q  == Some (P * n^-1, n != 0 :: cs) when n has no omega,    *)
(*                      q * P = n (cyc_eqb), n^-1 by nf_inv (conditions cs)   *)
(*   cyc_inv_atom a  == cyc_inv_exact, else cyc_inv_norm, on a = AInv e,      *)
(*                      q = pnorm e                                           *)
(*   cyc_inv_nf p    == p with the inverse atoms replaced, and the conditions *)
(*   cyc_nz c, cyc_cfilter cs == c is e != 0 with cyc_inv_exact (pnorm e),    *)
(*                      the conditions of cs not cyc_nz (q * v = 1 -> q != 0) *)
(*   radcan_check_cyc2 e1 e2 == radcan_check_cyc, else the normal forms of    *)
(*                      modes MNegC, MNegCW compared by cyc_eqb after         *)
(*                      cyc_inv_nf; the conditions filtered by cyc_cfilter    *)
(*   radcan_eq_cond_cyc2, radcan_eq_cyc2, radcan_eq_refined_cyc2 == the       *)
(*                      decision theorems (same hypotheses cycroot w,         *)
(*                      cycprim w as radcan_eq_cond_cyc), versions on C       *)
(*   cyc_cfilter_cyc == all_conds (cyc_cfilter cs) -> all_conds cs, given     *)
(*                      cycroot w and cycprim w (used in Dispatch.v)          *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts RootC Syntax Radcan Refine.
From Radcan Require Import RealRoot OmegaRoot2 CycC Cyclo CycloC.
Import Order.TTheory GRing.Theory Num.Theory ZNum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* The candidate inverse (unverified) *)

Definition omega_only (q : nf) : bool :=
  all (fun t => nilp (vsplit_omega t.2.1).2) q.

Definition key_coef (k : key) (p : nf) : coef :=
  foldr (fun t acc => if cmp_eqb (key_cmp t.2 k) then t.1 else acc) c_zero p.

Definition cyc_max_dim := 96%N.

Definition cyc_inv_cand (q : nf) : option nf :=
  let N := Pos.of_nat (foldr lcmn 1%N (omega_idx q)) in
  let m := (2 * Pos.to_nat N)%N in
  if cyc_cert m is Some phi then
    let tbl := ctab phi [:: Zpos 1] m in
    let bl := nf_bases q in
    let D := (size phi).-1 in
    if (D * foldr (fun bn a => bn.2 * a) 1 bl > cyc_max_dim)%N then None
    else
    let keys := [seq (vsingle (ARoot N omega_c) j, b) |
                   j <- iota 0 D, b <- nf_basis bl] in
    let cols := map (fun k => cyc_nf N tbl (nf_mul q [:: (c_one, k)])) keys in
    let rows := map (fun k => rcons (map (key_coef k) cols)
                                    (key_coef k nf_one)) keys in
    if gauss 0 (size keys) [::] rows is Some sol then
      Some (foldr (fun kv acc =>
                     nf_add (nf_single (last c_zero kv.2) kv.1) acc)
                  [::] (zip keys sol))
    else None
  else None.

(* The checked replacement of the inverse atoms *)

(* exact inverse: q * v = 1 modulo Phi_2N, q omega-only *)
Definition cyc_inv_exact (q : nf) : option nf :=
  if omega_only q && ~~ nilp (omega_idx q) then
    if cyc_inv_cand q is Some v then
      if cyc_eqb (nf_mul q v) nf_one then Some v else None
    else None
  else None.

(* the conjugate omega_N -> omega_N ^+ a (unverified, a candidate only) *)
Definition cyc_conj (N : positive) (a : nat) (q : nf) : nf :=
  let n := Pos.to_nat N in
  foldr (fun t acc =>
           let: (o, v) := vsplit_omega t.2.1 in
           let j := foldr (fun nk s => nk.2 * (n %/ Pos.to_nat nk.1) + s)%N
                          0%N o in
           let w := vsingle (ARoot N omega_c) ((a * j) %% (2 * n)) in
           nf_add [:: (t.1, (vmono_mul v w, t.2.2))] acc) [::] q.

(* P = the product of the conjugates a <> 1, n = q * P reduced (the norm) *)
Definition cyc_norm_cof (q : nf) : nf * nf :=
  let N := Pos.of_nat (foldr lcmn 1%N (omega_idx q)) in
  let M := (2 * Pos.to_nat N)%N in
  if cyc_cert M is Some phi then
    let tbl := ctab phi [:: Zpos 1] M in
    let P := foldr (fun a acc => cyc_nf N tbl (nf_mul (cyc_conj N a q) acc))
                   nf_one [seq a <- iota 2 (M - 2) | coprime a M] in
    (P, cyc_nf N tbl (nf_mul q P))
  else (nf_one, q).

(* q^-1 = P * n^-1 when q * P = n (checked), n free of omegas, n != 0 *)
Definition cyc_inv_norm (q : nf) : option (nf * seq cond) :=
  let: (P, n) := cyc_norm_cof q in
  if [&& nilp (omega_idx n), ~~ nilp n, nf_wf n & cyc_eqb (nf_mul q P) n]
  then let: (w, cs) := nf_inv (nf_to_rexpr n) n in
       Some (nf_mul P w, CNeq0 (nf_to_rexpr n) :: cs)
  else None.

Definition cyc_inv_atom (a : atom) : option (nf * seq cond) :=
  if a is AInv e then
    let q := RadcanZ.pnorm e in
    if nilp (omega_idx q) then None
    else if cyc_inv_exact q is Some v then Some (v, [::])
    else cyc_inv_norm q
  else None.

Definition cyc_inv_term (t : coef * key) : nf * seq cond :=
  foldr (fun ak acc =>
           if cyc_inv_atom ak.1 is Some (v, cs) then
             (nf_mul (nf_pow v ak.2) acc.1, cs ++ acc.2)
           else (nf_mul [:: (c_one, ([:: ak], [::]))] acc.1, acc.2))
        ([:: (t.1, ([::], t.2.2))], [::]) t.2.1.

Definition cyc_inv_nf (p : nf) : nf * seq cond :=
  foldr (fun t acc => let: (q, cs) := cyc_inv_term t in
                      (nf_add q acc.1, cs ++ acc.2)) ([::], [::]) p.

Arguments cyc_inv_cand : simpl never.
Arguments cyc_inv_exact : simpl never.
Arguments cyc_inv_norm : simpl never.
Arguments cyc_inv_atom : simpl never.
Arguments cyc_inv_term : simpl never.

(* The checkers *)

Definition radcan_check_cyc2_bs (rt : bool) (m : rmode) (hs bs : seq nf)
  (e1 e2 : rexpr) : option (seq cond) :=
  let: (p1, p2, cs) := radcan_nfb rt m hs bs e1 e2 in
  let: (q1, c1) := cyc_inv_nf p1 in
  let: (q2, c2) := cyc_inv_nf p2 in
  if cyc_eqb q1 q2 then Some (cdedup (cs ++ c1 ++ c2)) else None.

Definition radcan_check_cyc2_m (m : rmode) (e1 e2 : rexpr) :
    option (seq cond) :=
  let cb := const_basis (rconsts m e1 ++ rconsts m e2) in
  let f1 := cb_rw m cb e1 in let f2 := cb_rw m cb e2 in
  let hs := neg_hints [:: f1; f2] in
  let ck rt := radcan_check_cyc2_bs rt m hs (mk_basis_n rt m hs [:: f1; f2])
                 f1 f2 in
  if ck false is Some cs then Some cs else ck true.

(* the conditions e != 0 with e invertible by cyc_inv_atom are dropped *)
Definition cyc_nz (c : cond) : bool :=
  if c is CNeq0 e then isSome (cyc_inv_exact (RadcanZ.pnorm e)) else false.

Definition cyc_cfilter (cs : seq cond) : seq cond :=
  filter (fun c => ~~ cyc_nz c) cs.

Definition radcan_check_cyc2_raw (e1 e2 : rexpr) : option (seq cond) :=
  if radcan_check_cyc e1 e2 is Some cs then Some cs
  else if radcan_check_cyc2_m MNegC e1 e2 is Some cs then Some cs
  else radcan_check_cyc2_m MNegCW e1 e2.

Definition radcan_check_cyc2 (e1 e2 : rexpr) : option (seq cond) :=
  if radcan_check_cyc2_raw e1 e2 is Some cs then Some (cyc_cfilter cs)
  else None.

Local Open Scope ring_scope.

(* An element with a right inverse is nonzero, and that is its inverse *)

Lemma mulr1_neq0 (F : fieldType) (u v : F) : u * v = 1 -> u != 0.
Proof.
by move=> uv; apply/eqP => u0; move: uv; rewrite u0 mul0r => /eqP;
  rewrite eq_sym oner_eq0.
Qed.

Lemma mulr1_inv (F : fieldType) (u v : F) : u * v = 1 -> u^-1 = v.
Proof.
move=> uv; have u0 := mulr1_neq0 uv.
by rewrite -[RHS]mul1r -(mulVf u0) -mulrA uv mulr1.
Qed.

(* Soundness *)

Lemma In_filter (T : Type) (P : pred T) x s :
  List.In x s -> P x -> List.In x (filter P s).
Proof.
elim: s => [|y s IH] //= [<- Px|/IH H Px]; first by rewrite Px; left.
by case: ifP => _; [right|]; exact: H.
Qed.

Section CycInvSound.

Variables (F : numFieldType) (r : posroot F) (env : seq F).
Hypotheses (hw : windex r) (hp : wprim r).

Local Notation nf_interp := (nf_interp r env).
Local Notation vmono_interp := (vmono_interp r env).
Local Notation key_interp := (key_interp r env).
Local Notation atom_interp := (atom_interp r env).

Local Arguments nf_add : simpl never.
Local Arguments nf_mul : simpl never.
Local Arguments nf_pow : simpl never.

Lemma cyc_inv_exact_mul q v : cyc_inv_exact q = Some v ->
  nf_interp q * nf_interp v = 1.
Proof.
rewrite /cyc_inv_exact; case: ifP => // _; case: (cyc_inv_cand q) => // v'.
case: ifP => // /(cyc_eqb_sound env hw hp) H [<-].
by move: H; rewrite nf_mul_sound nf_one_sound.
Qed.

Lemma cyc_inv_norm_sound q v cs : cyc_inv_norm q = Some (v, cs) ->
  holds r env cs -> nf_interp v = (nf_interp q)^-1.
Proof.
rewrite /cyc_inv_norm; case: (cyc_norm_cof q) => P n.
case: ifP => // /and4P[_ _ Hw /(cyc_eqb_sound env hw hp)].
rewrite nf_mul_sound => HqP.
have := nf_inv_sound (nf_to_rexpr_sound r env Hw).
case: (nf_inv _ _) => w cs' /= Hinv [<- <-] /holds_cons [/= Hn /Hinv Hw'].
move: Hn; rewrite (nf_to_rexpr_sound r env Hw) -HqP mulf_eq0 negb_or.
case/andP => Hq HP; rewrite nf_mul_sound Hw' -HqP invfM mulrCA.
by rewrite divff // mulr1.
Qed.

Lemma cyc_inv_atom_sound a v cs : cyc_inv_atom a = Some (v, cs) ->
  holds r env cs -> nf_interp v = atom_interp a.
Proof.
case: a => // e; rewrite /cyc_inv_atom /= RadcanZ.pnorm_sound.
set q := RadcanZ.pnorm e; case: ifP => // _.
case E : (cyc_inv_exact q) => [v'|]; last exact: cyc_inv_norm_sound.
by case=> <- _ _; apply/esym/mulr1_inv/cyc_inv_exact_mul.
Qed.

Lemma cyc_nz_sound c : cyc_nz c -> cond_interp r env c.
Proof.
case: c => // e; rewrite /cyc_nz /= RadcanZ.pnorm_sound.
by case E : (cyc_inv_exact _) => [v|] // _; exact: mulr1_neq0
  (cyc_inv_exact_mul E).
Qed.

Lemma holds_all_conds cs : holds r env cs -> all_conds r env cs.
Proof.
elim: cs => [|c cs IH] //= /holds_cons [Hc /IH Hcs].
by case: cs IH Hcs.
Qed.

Lemma cyc_cfilter_sound cs :
  all_conds r env (cyc_cfilter cs) -> all_conds r env cs.
Proof.
move=> /all_condsP H; apply: holds_all_conds => c Hc.
case Ez : (cyc_nz c); first exact: cyc_nz_sound.
by apply: H; apply: In_filter Hc _; rewrite Ez.
Qed.

Lemma cyc_inv_term_sound t : holds r env (cyc_inv_term t).2 ->
  nf_interp (cyc_inv_term t).1 = C2F t.1 * key_interp t.2.
Proof.
case: t => c [v m]; rewrite /cyc_inv_term /key_interp [(_, _).1]/= [(_, _).2]/=.
elim: v => [|ak v IH] /=.
  rewrite nf_interp_cons nf_interp_nil addr0 /key_interp /=.
  by rewrite vmono_interp_nil mul1r.
move: IH; set A := foldr _ _ v => IH.
rewrite vmono_interp_cons.
case E : (cyc_inv_atom ak.1) => [[w cs]|] /=.
  case/holds_cat => /(cyc_inv_atom_sound E) Hw /IH {}IH.
  by rewrite nf_mul_sound nf_pow_sound Hw IH mulrCA !mulrA.
move/IH => {}IH; rewrite nf_mul_sound IH nf_interp_cons nf_interp_nil addr0.
rewrite C2F_c_one mul1r /key_interp /= vmono_interp_cons vmono_interp_nil.
by rewrite mono_interp_nil !mulr1 mulrCA !mulrA.
Qed.

Lemma cyc_inv_nf_sound p : holds r env (cyc_inv_nf p).2 ->
  nf_interp (cyc_inv_nf p).1 = nf_interp p.
Proof.
elim: p => [|t p IH] //=.
have := @cyc_inv_term_sound t; case: (cyc_inv_term t) => q cs /= Ht.
case/holds_cat => /Ht {}Ht /IH {}IH.
by rewrite nf_add_sound IH Ht nf_interp_cons.
Qed.

Variable m : rmode.
Hypotheses (Hng : neg_mode m -> negroot r) (Hcy : cyc_mode m -> windex r).
Hypothesis Ho : odd_mode m -> oddroot r.
Hypothesis Hrl : real_mode m -> realroot r.

Lemma radcan_check_cyc2_bs_sound rt hs bs e1 e2 cs :
  radcan_check_cyc2_bs rt m hs bs e1 e2 = Some cs ->
  all_conds r env cs -> rinterp r env e1 = rinterp r env e2.
Proof.
have H1 := @normcr_sound F r env m Ho Hng Hrl Hcy rt hs bs e1.
have H2 := @normcr_sound F r env m Ho Hng Hrl Hcy rt hs bs e2.
set n1 := normcr rt m hs bs e1 in H1 *; set n2 := normcr rt m hs bs e2 in H2 *.
have E : radcan_check_cyc2_bs rt m hs bs e1 e2 =
    let: (q1, c1) := cyc_inv_nf n1.1 in let: (q2, c2) := cyc_inv_nf n2.1 in
    if cyc_eqb q1 q2 then
      Some (cdedup (cfilter m (cdedup (n1.2 ++ n2.2)) ++ c1 ++ c2))
    else None.
  clear H1 H2; rewrite /radcan_check_cyc2_bs /radcan_nfb -/n1 -/n2.
  by case: n1 => [? ?]; case: n2 => [? ?].
rewrite E; have := @cyc_inv_nf_sound n1.1.
case: (cyc_inv_nf n1.1) => q1 c1 N1; have := @cyc_inv_nf_sound n2.1.
case: (cyc_inv_nf n2.1) => q2 c2 N2.
have {}N1 : holds r env c1 -> nf_interp q1 = nf_interp n1.1 := N1.
have {}N2 : holds r env c2 -> nf_interp q2 = nf_interp n2.1 := N2.
case: ifP => // /(cyc_eqb_sound env hw hp) Hp [<-].
move=> /all_condsP /holds_dedup /holds_cat [+ /holds_cat [/N1 {}N1 /N2 {}N2]].
move=> /(cfilter_sound Hrl) /holds_dedup /holds_cat.
by case=> /H1 -> /H2 ->; rewrite -N1 -N2 Hp.
Qed.

Lemma radcan_check_cyc2_m_sound e1 e2 cs :
  radcan_check_cyc2_m m e1 e2 = Some cs ->
  all_conds r env cs -> rinterp r env e1 = rinterp r env e2.
Proof.
rewrite /radcan_check_cyc2_m; set cb := const_basis _.
rewrite -(cb_rw_sound env Ho Hng cb e1) -(cb_rw_sound env Ho Hng cb e2).
by case/ocase_some => /radcan_check_cyc2_bs_sound.
Qed.

End CycInvSound.

(* The decision theorems *)

Theorem radcan_eq_cond_cyc2 (F : numFieldType) (r : posroot F)
    (w : negroot r) (cy : cycroot w) (cp : cycprim w) (env : seq F)
    e1 e2 cs :
  radcan_check_cyc2 e1 e2 = Some cs -> all_conds r env cs ->
  rinterp r env e1 = rinterp r env e2.
Proof.
have hw := cycroot_windex cy; have hp := cycprim_wprim cp.
rewrite /radcan_check_cyc2.
case E : (radcan_check_cyc2_raw e1 e2) => [cs'|] // [<-].
move=> /(cyc_cfilter_sound hw hp); move: E.
rewrite /radcan_check_cyc2_raw; case/ocase_some => H.
  exact: (radcan_eq_cond_cyc cy cp H).
by case/ocase_some: H => H; apply: (radcan_check_cyc2_m_sound hw hp _ _ _ _ H).
Qed.

Theorem radcan_eq_cyc2 (F : numFieldType) (r : posroot F) (w : negroot r)
    (cy : cycroot w) (cp : cycprim w) (env : seq F) e1 e2 :
  radcan_check_cyc2 e1 e2 = Some [::] -> rinterp r env e1 = rinterp r env e2.
Proof. by move/(radcan_eq_cond_cyc2 cy cp); apply. Qed.

Theorem radcan_eq_refined_cyc2 (F : numFieldType) (r : posroot F)
    (w : negroot r) (cy : cycroot w) (cp : cycprim w) (env : seq F)
    e1 e2 cs rcs :
  radcan_check_cyc2 e1 e2 = Some cs -> refine cs = rcs ->
  all_rconds F (proot r) env rcs -> rinterp r env e1 = rinterp r env e2.
Proof.
move=> H Hr Hc; apply: (radcan_eq_cond_cyc2 cy cp H).
by apply: all_conds_bridge_back; apply: refine_sound; rewrite Hr.
Qed.

Lemma cyc_cfilter_cyc (F : numFieldType) (r : posroot F) (env : seq F)
    (w : negroot r) (cy : cycroot w) (cp : cycprim w) cs :
  all_conds r env (cyc_cfilter cs) -> all_conds r env cs.
Proof.
exact: (cyc_cfilter_sound (cycroot_windex cy) (cycprim_wprim cp)).
Qed.

(* On C: n.-root goals *)

Section CycloInvC.

Variable C : numClosedFieldType.

Theorem radcan_eq_cond_rootC_cyc2 (env : seq C) e1 e2 cs :
  radcan_check_cyc2 e1 e2 = Some cs -> all_conds (rootC_posroot C) env cs ->
  rinterp (rootC_posroot C) env e1 = rinterp (rootC_posroot C) env e2.
Proof. exact: (radcan_eq_cond_cyc2 (rootC_cycroot C) (rootC_cycprim C)). Qed.

Theorem radcan_eq_refined_rootC_cyc2 (env : seq C) e1 e2 cs rcs :
  radcan_check_cyc2 e1 e2 = Some cs -> refine cs = rcs ->
  all_rconds C (proot (rootC_posroot C)) env rcs ->
  rinterp (rootC_posroot C) env e1 = rinterp (rootC_posroot C) env e2.
Proof.
exact: (radcan_eq_refined_cyc2 (rootC_cycroot C) (rootC_cycprim C)).
Qed.

End CycloInvC.
