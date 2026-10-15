(******************************************************************************)
(* CondSimp: modes, and the simplification with side conditions.              *)
(*   rmode            == MStd (any posroot), MOdd (needs an oddroot: real odd *)
(*                      roots), MNeg (needs a negroot: roots of -1, as on C)  *)
(*                      MNegW (MNeg preferring omega_n to a flipped base),    *)
(*                      MReal (needs a realroot: odd roots without sign       *)
(*                      conditions), MRealA (MReal, and |B| = proot 2 (B^2)   *)
(*                      for even roots of even powers, no condition)          *)
(*   nf_simp m p      == reduce proot n B ^+ k (n <= k); merge proot n B,     *)
(*                      proot m B over lcm n m and reduce the index by        *)
(*                      gcd k n (0 <= B); cancel P * D^-1 by exact division   *)
(*                      or through G = gcd P D (condition G != 0)             *)
(*   nf_simp_sound    == soundness of nf_simp under its conditions            *)
(* omega_n = proot n (-1), omega_n ^+ n = -1; omega atoms of different        *)
(* indices are never merged.                                                  *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt ZArith Lia.
From Stdlib Require Import QArith_base Qreduction.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts Syntax Backend Mono Factor NF.
From Radcan Require Import Inverse Poly Ratio RealRoot.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* MNegW: MNeg preferring omega_n to a flipped base (fallback of MNeg)
   MReal: real field (realroot), odd roots of any sign split and reduced
   without condition; MRealA: the same, and even roots of even powers give
   absolute values |B| = proot 2 (B ^+ 2) (no condition) *)
Inductive rmode := MStd | MOdd | MNeg | MNegW | MReal | MRealA.

Definition odd_mode (m : rmode) : bool :=
  match m with MOdd | MReal | MRealA => true | _ => false end.
Definition neg_mode (m : rmode) : bool :=
  match m with MNeg | MNegW => true | _ => false end.
Definition real_mode (m : rmode) : bool :=
  match m with MReal | MRealA => true | _ => false end.
Definition abs_mode (m : rmode) : bool := if m is MRealA then true else false.
Definition negw_mode (m : rmode) : bool := if m is MNegW then true else false.

(* the radicand -1: ARoot n omega_c is omega_n = proot n (-1) *)
Definition omega_c : rexpr := RCst (Zneg xH).
Definition is_omega (e : rexpr) : bool :=
  if e is RCst (Zneg xH) then true else false.

Lemma is_omegaP e : is_omega e -> e = omega_c.
Proof. by case: e => // -[] // -[]. Qed.


Module CondSimpF (Import N : NUM).

Include RatioF N.

(* Simplification: proot n B ^+ k with n <= k, and cancellation P * D^-1 *)

Fixpoint vextract (v : vmono) : option (positive * rexpr * nat * vmono) :=
  match v with
  | [::] => None
  | (a, k) :: v' =>
    let rest := if vextract v' is Some (n', e', k', w) then
                  Some (n', e', k', (a, k) :: w) else None in
    if a is ARoot n e then
      (if (Pos.to_nat n <= k)%N then Some (n, e, k, v') else rest)
    else rest
  end.

(* vmerge rewrites, for 0 <= e, with L = lcm n m and g = gcd k n > 1,
     proot n e ^+ k1 * proot m e ^+ k2  into  proot L e ^+ (k1 L/n + k2 L/m)
     proot n e ^+ k  into  proot (n/g) e ^+ (k/g) *)
Fixpoint vfind_root (e : rexpr) (v : vmono) :
  option (positive * nat * vmono) :=
  match v with
  | [::] => None
  | (a, k) :: v' =>
    let rest := if vfind_root e v' is Some (m, k', w) then
                  Some (m, k', (a, k) :: w) else None in
    if a is ARoot m e' then
      (if cmp_eqb (rexpr_cmp e e') then Some (m, k, v') else rest)
    else rest
  end.

(* in mode MNeg the atoms omega_n are never merged (no index law) *)
Fixpoint vmerge (m : rmode) (v : vmono) :
  option (positive * rexpr * nat * vmono) :=
  match v with
  | [::] => None
  | (a, k) :: v' =>
    let rest := if vmerge m v' is Some (n', e', k', w) then
                  Some (n', e', k', (a, k) :: w) else None in
    if a is ARoot n e then
      if neg_mode m && is_omega e then rest else
      let N := Pos.to_nat n in
      if vfind_root e v' is Some (m, k2, w) then
        let M := Pos.to_nat m in
        let L := lcmn N M in
        Some (Pos.of_nat L, e, (k * (L %/ N) + k2 * (L %/ M))%N, w)
      else
        let g := gcdn k N in
        if (1 < g)%N then Some (Pos.of_nat (N %/ g), e, (k %/ g)%N, v')
        else rest
    else rest
  end.

Definition reducible (m : rmode) (v : vmono) : bool :=
  if vextract v is Some _ then true else
  if vmerge m v is Some _ then true else false.

(* proot n e ^+ k = e ^+ (k / n) * proot n e ^+ (k mod n) needs 0 <= e,
   except for omega_n in mode MNeg *)
Definition ge0_cond (m : rmode) (e : rexpr) : seq cond :=
  if neg_mode m && is_omega e then [::] else [:: CGe0 e].

(* mode MReal: odd roots need no sign condition *)
Definition ge0_condn (m : rmode) (n : positive) (e : rexpr) : seq cond :=
  if real_mode m && odd (Pos.to_nat n) then [::] else ge0_cond m e.

(* every root of e in v has an odd index *)
Definition vodd_root (e : rexpr) (v : vmono) : bool :=
  all (fun ak => if ak.1 is ARoot n e' then
                   cmp_eqb (rexpr_cmp e e') ==> odd (Pos.to_nat n)
                 else true) v.

Definition merge_cond (m : rmode) (e : rexpr) (v : vmono) : seq cond :=
  if real_mode m && vodd_root e v then [::] else [:: CGe0 e].

Definition reduce_term (m : rmode) (t : coef * key) : nf * seq cond :=
  if vextract t.2.1 is Some (n, e, k, w) then
    let N := Pos.to_nat n in
    (nf_mul [:: (t.1, (vmono_mul (vsingle (ARoot n e) (k %% N)) w, t.2.2))]
            (nf_pow (pnorm e) (k %/ N)), ge0_condn m n e)
  else if vmerge m t.2.1 is Some (n, e, k, w) then
    ([:: (t.1, (vmono_mul (vsingle (ARoot n e) k) w, t.2.2))],
     merge_cond m e t.2.1)
  else ([:: t], [::]).

Definition nf_reduce1 (m : rmode) (p : nf) : nf * seq cond :=
  foldr (fun t acc => let: (q, cs) := reduce_term m t in
                      (nf_add q acc.1, cs ++ acc.2)) ([::], [::]) p.

Fixpoint nf_reduce_n (m : rmode) (fuel : nat) (p : nf) : nf * seq cond :=
  match fuel with
  | O => (p, [::])
  | S f =>
    if has (fun t => reducible m t.2.1) p then
      let: (q, cs) := nf_reduce1 m p in
      let: (q', cs') := nf_reduce_n m f q in (q', cs ++ cs')
    else (p, [::])
  end.

Fixpoint vstrip (v : vmono) (a : atom) : option vmono :=
  match v with
  | [::] => None
  | (b, k) :: v' =>
    if cmp_eqb (atom_cmp a b) && (0 < k)%N then
      Some (if k == 1%N then v' else (b, k.-1) :: v')
    else if vstrip v' a is Some w then Some ((b, k) :: w) else None
  end.

(* p = P * a + R *)
Definition split_inv (a : atom) (p : nf) : nf * nf :=
  foldr (fun t acc => if vstrip t.2.1 a is Some w then
                        (nf_add [:: (t.1, (w, t.2.2))] acc.1, acc.2)
                      else (acc.1, nf_add [:: t] acc.2)) ([::], [::]) p.

(* each inverse atom as many times as its exponent: x^3 / x^3 needs three
   cancellations *)
Definition inv_atoms (p : nf) : seq rexpr :=
  flatten (map (fun t =>
                  flatten (map (fun ak => if ak.1 is AInv e then nseq ak.2 e
                                          else [::])
                               t.2.1)) p).

(* P = sum_m P_m * m with root monomials m, each P_m divided by the
   polynomial D (to be checked) *)
Definition monos_of (p : nf) : seq mono :=
  foldr (fun t acc =>
           if has (fun m => cmp_eqb (mono_cmp m t.2.2)) acc then acc
           else t.2.2 :: acc) [::] p.

Definition pdiv_m (P D : nf) : option nf :=
  if pdiv P D is Some q then Some q else
  if ispoly D then
    foldr (fun m acc =>
             if acc is Some q then
               let Pm := map (fun t => (t.1, (t.2.1, [::])))
                             (filter (fun t => cmp_eqb (mono_cmp t.2.2 m)) P) in
               if pdiv Pm D is Some qm then
                 Some (nf_add (nf_mul qm [:: (c_one, ([::], m))]) q)
               else None
             else None) (Some [::]) (monos_of P)
  else None.

Definition cancel_one (p : nf) (e : rexpr) : option (nf * cond) :=
  let: (P, R) := split_inv (AInv e) p in
  let D := pnorm e in
  if P is [::] then None else
  if pdiv_m P D is Some Qt then
    if nf_eqb P (nf_mul Qt D) then Some (nf_add Qt R, CNeq0 e) else None
  else if gcd_split P D is Some (G, P', D') then
    (* P / D = P' / D' when P = P' G, D = D' G and G != 0 *)
    let: (Di, cs) := nf_inv (nf_to_rexpr D') D' in
    if [&& nf_eqb P (nf_mul P' G), nf_eqb D (nf_mul D' G), nf_wf D',
           nf_wf G & nilp cs]
    then Some (nf_add (nf_mul P' Di) R, CNeq0 (nf_to_rexpr G)) else None
  else None.

Definition nf_cancel (p : nf) : nf * seq cond :=
  foldl (fun acc e => if cancel_one acc.1 e is Some (q, c)
                      then (q, rcons acc.2 c) else acc)
        (p, [::]) (inv_atoms p).

Definition nf_simp (m : rmode) (p : nf) : nf * seq cond :=
  let: (q, c1) := nf_reduce_n m 16 p in
  let: (s, c2) := nf_cancel q in (s, c1 ++ c2).

Local Open Scope ring_scope.

Section CondSimpSound.

Variable F : numFieldType.
Variable r : posroot F.
Variable env : seq F.
(* odd mode: only used with an oddroot, neg mode: only with a negroot *)
Variable mo : rmode.
Hypothesis Ho : odd_mode mo -> oddroot r.
Hypothesis Hng : neg_mode mo -> negroot r.
Hypothesis Hrl : real_mode mo -> realroot r.

Local Notation fct_interp := (fct_interp r).
Local Notation mono_interp := (mono_interp r).
Local Notation atom_interp := (atom_interp r env).
Local Notation vmono_interp := (vmono_interp r env).
Local Notation key_interp := (key_interp r env).
Local Notation holds := (holds r env).
Local Notation nf_interp := (nf_interp r env).

Local Notation cond_interp := (cond_interp r env).
Local Notation all_conds := (all_conds r env).

Local Arguments nf_mul : simpl never.
Local Arguments nf_add : simpl never.
Local Arguments nf_pow : simpl never.
Local Arguments nf_opp : simpl never.

Lemma vextract_sound v n e k w : vextract v = Some (n, e, k, w) ->
  vmono_interp v = atom_interp (ARoot n e) ^+ k * vmono_interp w.
Proof.
elim: v n e k w => [|[a k'] v IH] n e k w //=.
have Hrest : (if vextract v is Some (n', e', k'', w') then
                Some (n', e', k'', (a, k') :: w') else None) =
             Some (n, e, k, w) ->
             vmono_interp ((a, k') :: v) =
             atom_interp (ARoot n e) ^+ k * vmono_interp w.
  case E : (vextract v) => [[[[n1 e1] k1] w1]|] // [<- <- <- <-].
  by rewrite !vmono_interp_cons (IH _ _ _ _ E) mulrCA.
case: a Hrest => [i|e'|n' e'] Hrest //.
by case: ifP => _ // [<- <- <- <-]; rewrite vmono_interp_cons.
Qed.

Lemma vfind_root_sound e v m k w : vfind_root e v = Some (m, k, w) ->
  vmono_interp v = atom_interp (ARoot m e) ^+ k * vmono_interp w.
Proof.
elim: v m k w => [|[a k'] v IH] m k w //=.
have Hrest : (if vfind_root e v is Some (m', k'', w') then
                Some (m', k'', (a, k') :: w') else None) = Some (m, k, w) ->
             vmono_interp ((a, k') :: v) =
             atom_interp (ARoot m e) ^+ k * vmono_interp w.
  case E : (vfind_root e v) => [[[m1 k1] w1]|] // [<- <- <-].
  by rewrite !vmono_interp_cons (IH _ _ _ E) mulrCA.
case: a Hrest => [i|e'|m' e'] Hrest //.
case: ifP => [/cmp_eqbP/rexpr_cmp_eq <- [<- <- <-]|_ /Hrest //].
by rewrite vmono_interp_cons.
Qed.

Lemma proot_expr_div n g k a :
  (0 < n)%N -> (0 < g)%N -> (g %| n)%N -> (g %| k)%N ->
  0 <= a -> proot r n a ^+ k = proot r (n %/ g) a ^+ (k %/ g).
Proof.
move=> n0 g0 gn gk a0.
have ng0 : (0 < n %/ g)%N by rewrite divn_gt0 // dvdn_leq.
by rewrite -(proot_exprMn r _ ng0 g0 a0) !divnK.
Qed.

Lemma vmerge_sound v n e k w : vmerge mo v = Some (n, e, k, w) ->
  0 <= rinterp r env e ->
  vmono_interp v = atom_interp (ARoot n e) ^+ k * vmono_interp w.
Proof.
elim: v n e k w => [|[a k'] v IH] n e k w //=.
have Hrest : (if vmerge mo v is Some (n', e', k'', w') then
                Some (n', e', k'', (a, k') :: w') else None) =
             Some (n, e, k, w) ->
             0 <= rinterp r env e ->
             vmono_interp ((a, k') :: v) =
             atom_interp (ARoot n e) ^+ k * vmono_interp w.
  case E : (vmerge mo v) => [[[[n1 e1] k1] w1]|] // [<- <- <- <-] He.
  by rewrite !vmono_interp_cons (IH _ _ _ _ E He) mulrCA.
case: a Hrest => [i|e'|n' e'] Hrest //.
case: ifP => [_ /Hrest //|_].
have N0 : (0 < Pos.to_nat n')%N by apply/ssrnat.ltP; exact: Pos2Nat.is_pos.
case Ef : (vfind_root e' v) => [[[m k2] w2]|].
  have M0 : (0 < Pos.to_nat m)%N by apply/ssrnat.ltP; exact: Pos2Nat.is_pos.
  move=> [<- <- <- <-] He.
  have L0 : (0 < lcmn (Pos.to_nat n') (Pos.to_nat m))%N by rewrite lcmn_gt0 N0.
  rewrite vmono_interp_cons (vfind_root_sound Ef) mulrA /=.
  rewrite Nat2Pos.id; last first.
    by apply/eqP; rewrite -lt0n.
  by rewrite exprD -!proot_expr_lift ?dvdn_lcml ?dvdn_lcmr.
case: ifP => [g1 [<- <- <- <-] He|_ /Hrest //].
have g0 : (0 < gcdn k' (Pos.to_nat n'))%N by rewrite gcdn_gt0 N0 orbT.
have Ng0 : (0 < Pos.to_nat n' %/ gcdn k' (Pos.to_nat n'))%N.
  by rewrite divn_gt0 // dvdn_leq // dvdn_gcdr.
rewrite vmono_interp_cons /= Nat2Pos.id; last by apply/eqP; rewrite -lt0n.
by rewrite -proot_expr_div ?dvdn_gcdr ?dvdn_gcdl.
Qed.

Lemma expr_divmodK (x a : F) N k :
  x ^+ N = a -> x ^+ k = a ^+ (k %/ N) * x ^+ (k %% N).
Proof. by move=> H; rewrite {1}(divn_eq k N) exprD mulnC exprM H. Qed.

(* the n-th root of e to the n is e: 0 <= e, or e = -1 in mode MNeg *)
Lemma ge0_condK n e : holds (ge0_cond mo e) ->
  proot r (Pos.to_nat n) (rinterp r env e) ^+ Pos.to_nat n = rinterp r env e.
Proof.
have N0 : (0 < Pos.to_nat n)%N by apply/ssrnat.ltP; exact: Pos2Nat.is_pos.
rewrite /ge0_cond.
case: ifP => [/andP[Hn /is_omegaP ->] _|_ /holds_cons [He _]].
  have w : negroot r by apply: Hng; case: (mo) Hn.
  by rewrite /= pos2F1 prootN1K.
exact: prootK.
Qed.

(* mode MReal: odd roots of any sign *)

Lemma ge0_condnK n e : holds (ge0_condn mo n e) ->
  proot r (Pos.to_nat n) (rinterp r env e) ^+ Pos.to_nat n = rinterp r env e.
Proof.
rewrite /ge0_condn; case: ifP => [/andP[Hm On] _|_]; last exact: ge0_condK.
exact: (proot_oddK (Hrl Hm)).
Qed.

Lemma vfind_root_odd e v m k w : vfind_root e v = Some (m, k, w) ->
  vodd_root e v -> odd (Pos.to_nat m).
Proof.
elim: v m k w => [|[a k'] v IH] m k w //=.
move=> H /andP[Ha Hv]; move: H.
have Hrest : (if vfind_root e v is Some (m', k'', w') then
                Some (m', k'', (a, k') :: w') else None) = Some (m, k, w) ->
             odd (Pos.to_nat m).
  by case E : (vfind_root e v) => [[[m1 k1] w1]|] // [<- _ _]; apply: IH E Hv.
case: a Hrest Ha => [i|e'|m' e'] Hrest //= Ha.
by case: ifP Ha => [_ /= Om [<- _ _] //|_ _ /Hrest].
Qed.

Lemma proot_expr_lift_odd (rl : realroot r) n l e a :
  (0 < n)%N -> (n %| l)%N -> odd l ->
  proot r n a ^+ e = proot r l a ^+ (e * (l %/ n)).
Proof.
move=> n0 nl Ol.
have El : (n * (l %/ n))%N = l by rewrite mulnC divnK.
by rewrite mulnC exprM -{1}El proot_odd_exprMn // El.
Qed.

Lemma proot_expr_div_odd (rl : realroot r) n g k a :
  (0 < g)%N -> (g %| n)%N -> (g %| k)%N -> odd n ->
  proot r n a ^+ k = proot r (n %/ g) a ^+ (k %/ g).
Proof.
move=> g0 gn gk On.
have En : (n %/ g * g)%N = n by rewrite divnK.
by rewrite -{1}(divnK gk) mulnC exprM -{1}En proot_odd_exprMn ?En.
Qed.

Lemma rexpr_cmp_refl e : rexpr_cmp e e = Eq.
Proof.
elim: e => [z|i|n p|n a IHa|a IHa b IHb|a IHa|a IHa b IHb|a IHa b IHb|
            a IHa k|a IHa] //=;
  by rewrite ?IHa ?IHb ?Z.compare_refl ?Nat.compare_refl ?Pos.compare_refl.
Qed.

Lemma odd_lcmn a b : odd a -> odd b -> odd (lcmn a b).
Proof.
move=> Oa Ob; apply: (@dvdn_odd _ (a * b)); last by rewrite oddM Oa.
by rewrite dvdn_lcm dvdn_mulr // dvdn_mull.
Qed.

Lemma vmerge_sound_odd (rl : realroot r) v n e k w :
  vmerge mo v = Some (n, e, k, w) -> vodd_root e v ->
  vmono_interp v = atom_interp (ARoot n e) ^+ k * vmono_interp w.
Proof.
elim: v n e k w => [|[a k'] v IH] n e k w //=.
have Hrest : (if vmerge mo v is Some (n', e', k'', w') then
                Some (n', e', k'', (a, k') :: w') else None) =
             Some (n, e, k, w) -> vodd_root e v ->
             vmono_interp ((a, k') :: v) =
             atom_interp (ARoot n e) ^+ k * vmono_interp w.
  case E : (vmerge mo v) => [[[[n1 e1] k1] w1]|] // [<- <- <- <-] He.
  by rewrite !vmono_interp_cons (IH _ _ _ _ E He) mulrCA.
case: a Hrest => [i|e'|n' e'] Hrest.
- by move=> H /andP[_ Hv]; apply: Hrest H Hv.
- by move=> H /andP[_ Hv]; apply: Hrest H Hv.
case: ifP => [_ H /andP[_ Hv]|_]; first exact: Hrest H Hv.
have N0 : (0 < Pos.to_nat n')%N by apply/ssrnat.ltP; exact: Pos2Nat.is_pos.
case Ef : (vfind_root e' v) => [[[m k2] w2]|].
  have M0 : (0 < Pos.to_nat m)%N by apply/ssrnat.ltP; exact: Pos2Nat.is_pos.
  move=> [<- <- <- <-] /andP[/= Hn Hv].
  move: Hn; rewrite rexpr_cmp_refl /= => On.
  have Om := vfind_root_odd Ef Hv.
  have L0 : (0 < lcmn (Pos.to_nat n') (Pos.to_nat m))%N by rewrite lcmn_gt0 N0.
  rewrite vmono_interp_cons (vfind_root_sound Ef) mulrA /=.
  rewrite Nat2Pos.id; last first.
    by apply/eqP; rewrite -lt0n.
  rewrite exprD -!(proot_expr_lift_odd rl) ?dvdn_lcml ?dvdn_lcmr //.
  1,2: exact: odd_lcmn.
case: ifP => [g1 [<- <- <- <-] /andP[/= Hn _]|_ H /andP[_ Hv]]; last first.
  exact: Hrest H Hv.
move: Hn; rewrite rexpr_cmp_refl /= => On.
have g0 : (0 < gcdn k' (Pos.to_nat n'))%N by rewrite gcdn_gt0 N0 orbT.
rewrite vmono_interp_cons /= Nat2Pos.id; last first.
  by apply/eqP; rewrite -lt0n divn_gt0 // dvdn_leq // dvdn_gcdr.
by rewrite -(proot_expr_div_odd rl) ?dvdn_gcdr ?dvdn_gcdl.
Qed.

Lemma reduce_term_sound t : holds (reduce_term mo t).2 ->
  nf_interp (reduce_term mo t).1 = C2F t.1 * key_interp t.2.
Proof.
case: t => c [v m]; rewrite /reduce_term /=.
case E : (vextract v) => [[[[n e] k] w]|] /=; last first.
  case Em : (vmerge mo v) => [[[[n e] k] w]|] /=; last first.
    by rewrite nf_interp_cons nf_interp_nil addr0.
  have Hv : holds (merge_cond mo e v) ->
     vmono_interp v = atom_interp (ARoot n e) ^+ k * vmono_interp w.
    rewrite /merge_cond; case: ifP => [/andP[Hm Hod] _|_].
      exact: (vmerge_sound_odd (Hrl Hm) Em).
    by case/holds_cons => /= He _; apply: vmerge_sound Em He.
  move/Hv => {}Hv.
  rewrite nf_interp_cons nf_interp_nil addr0 /key_interp /=.
  by rewrite vmono_mul_sound vsingle_sound Hv mulrA.
move=> /ge0_condnK He.
rewrite nf_mul_sound nf_pow_sound -pnorm_sound.
rewrite nf_interp_cons nf_interp_nil addr0.
rewrite /key_interp /= vmono_mul_sound vsingle_sound (vextract_sound E) /=.
rewrite (expr_divmodK k He).
move: (C2F c) (rinterp r env e ^+ _) (proot _ _ _ ^+ _) (vmono_interp w)
  (mono_interp m).
move=> a b x y z.
by rewrite -mulrA; congr (_ * _); rewrite mulrC !mulrA.
Qed.

Lemma nf_reduce1_sound p : holds (nf_reduce1 mo p).2 ->
  nf_interp (nf_reduce1 mo p).1 = nf_interp p.
Proof.
elim: p => [|t p IH] //=.
move: IH; rewrite /nf_reduce1 /=; case: (foldr _ _ p) => s cs' /= IH.
have := @reduce_term_sound t; case: (reduce_term mo t) => q cs /= Hr.
case/holds_cat => /Hr Hq /IH Hs.
by rewrite nf_add_sound Hq Hs nf_interp_cons.
Qed.

Lemma nf_reduce_n_sound f p : holds (nf_reduce_n mo f p).2 ->
  nf_interp (nf_reduce_n mo f p).1 = nf_interp p.
Proof.
elim: f p => [|f IH] p //=; case: ifP => // _.
have := @nf_reduce1_sound p; case: (nf_reduce1 mo p) => q cs /= Hq.
have := IH q; case: (nf_reduce_n mo f q) => q' cs' /= Hq'.
by case/holds_cat => /Hq <- /Hq'.
Qed.

(* cancellation P * D^-1 -> P / D *)

Lemma vstrip_sound v a w : vstrip v a = Some w ->
  vmono_interp v = atom_interp a * vmono_interp w.
Proof.
elim: v w => [|[b k] v IH] w //=.
case: ifP => [/andP[/cmp_eqbP/atom_cmp_eq <- k0] [<-]|_].
  case: eqP => [k1|k1]; rewrite vmono_interp_cons /=.
    by rewrite k1 expr1.
  by rewrite vmono_interp_cons /= mulrA -exprS prednK.
case E : (vstrip v a) => [w'|] // [<-].
by rewrite !vmono_interp_cons /= (IH _ E) mulrCA.
Qed.

Lemma split_inv_sound a p :
  nf_interp p = nf_interp (split_inv a p).1 * atom_interp a +
                nf_interp (split_inv a p).2.
Proof.
elim: p => [|[c [v m]] p IH] /=; first by rewrite !nf_interp_nil mul0r add0r.
case E : (vstrip v a) => [w|] /=;
  rewrite nf_interp_cons IH !nf_add_sound !nf_interp_cons !nf_interp_nil
          !addr0 /=.
  rewrite /key_interp /= (vstrip_sound E) mulrDl addrA; congr (_ + _ + _).
  move: (C2F c) (atom_interp a) (vmono_interp w) (mono_interp m) => x y z t.
  by rewrite -!mulrA; congr (_ * _); rewrite mulrC !mulrA.
by rewrite addrCA.
Qed.

Lemma cancel_one_sound p e q c :
  cancel_one p e = Some (q, c) -> cond_interp c ->
  nf_interp q = nf_interp p.
Proof.
rewrite /cancel_one; have := split_inv_sound (AInv e) p.
case: split_inv => P R /= Hs.
case: P Hs => [|t P] Hs //.
set P0 := t :: P in Hs *.
case: pdiv_m => [Qt|].
  case: ifP => // /nf_eqb_eq HP [<- <-] /= Hc.
  by rewrite Hs HP nf_add_sound nf_mul_sound -pnorm_sound mulfK.
case: gcd_split => [[[G P'] D']|] //.
have := @nf_inv_sound F r env (nf_to_rexpr D') D'.
case: nf_inv => Di cs HDi.
case: ifP => //.
move=> /and5P[/nf_eqb_eq HP /nf_eqb_eq HD wD wG /nilP Ecs] [<- <-] /=.
rewrite nf_to_rexpr_sound // => Hc.
rewrite Hs HP nf_add_sound !nf_mul_sound (pnorm_sound r env e) HD.
rewrite nf_mul_sound /=.
rewrite HDi ?nf_to_rexpr_sound // ?Ecs; last by move=> ? [].
by rewrite invfM mulrACA divff // mulr1.
Qed.

Lemma nf_cancel_sound p : holds (nf_cancel p).2 ->
  nf_interp (nf_cancel p).1 = nf_interp p.
Proof.
rewrite /nf_cancel.
have : forall l (acc : nf * seq cond),
    holds (foldl (fun acc e => if cancel_one acc.1 e is Some (q, c) then
                                 (q, rcons acc.2 c) else acc) acc l).2 ->
    holds acc.2 /\
    nf_interp (foldl (fun acc e => if cancel_one acc.1 e is Some (q, c) then
                                 (q, rcons acc.2 c) else acc) acc l).1 =
    nf_interp acc.1.
  elim=> [|e l IH] acc //=.
  case E : (cancel_one acc.1 e) => [[q c]|] /IH [] //=.
  rewrite -cats1 => /holds_cat [H1 H2] ->; split=> //.
  by apply: cancel_one_sound E _; apply: H2; left.
by move=> H /H [].
Qed.

Lemma nf_simp_sound p :
  holds (nf_simp mo p).2 -> nf_interp (nf_simp mo p).1 = nf_interp p.
Proof.
rewrite /nf_simp.
have := @nf_reduce_n_sound 16 p; case: nf_reduce_n => q c1 /= Hq.
have := @nf_cancel_sound q; case: nf_cancel => s c2 /= Hs.
by case/holds_cat => /Hq <- /Hs.
Qed.

End CondSimpSound.

End CondSimpF.
