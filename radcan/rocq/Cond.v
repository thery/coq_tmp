(******************************************************************************)
(* Cond: the normaliser with side conditions, and its soundness.              *)
(*   rmode            == MStd (any posroot), MOdd (needs an oddroot: real odd *)
(*                       roots), MNeg (needs a negroot: roots of -1, as on C) *)
(*                       MNegW (MNeg preferring omega_n to a flipped base),   *)
(*                       MReal (needs a realroot: odd roots without sign      *)
(*                       conditions), MRealA (MReal, and |B| = proot 2 (B^2)  *)
(*                       for even roots of even powers, no condition)         *)
(*   nf_simp m p      == reduce proot n B ^+ k (n <= k); merge proot n B,     *)
(*                       proot m B over lcm n m and reduce the index by       *)
(*                       gcd k n (0 <= B); cancel P * D^-1 by exact division  *)
(*                       or through G = gcd P D (condition G != 0)            *)
(*   nf_rootE m hs bs == root of a radicand split over the basis bs; MOdd:    *)
(*                       proot n (- a) = - proot n a for odd n; MNeg:         *)
(*                       proot n (- a) = proot n a * omega_n                  *)
(*   normc m hs bs e  == normal form of e and its side conditions             *)
(*   normcr true      == the same, with denominators mixing variables and     *)
(*                       roots rationalised (M11, Ratio.v); radcan_check_raw  *)
(*                       uses it only when the plain normal forms differ      *)
(*   normc0 e         == root-free normaliser (sound for any root function)   *)
(*   mk_basis_n       == basis of the radicands, plus the square-free factors *)
(*                       of nested radicands whose normal form is root-free   *)
(*   radcan_check e1 e2 == Some cs when both sides have the same normal form  *)
(*                       under the conditions cs; radcan_check_odd,           *)
(*                       radcan_check_neg: the same in modes MOdd, MNeg (then *)
(*                       MNegW); radcan_check_real: MRealA, then MReal        *)
(*   radcan_check_irr == the basis refined by irreducible factors (M16, form  *)
(*                       1, Poly.irr_basis): stronger conditions, so the      *)
(*                       checkers try it last (radcan_check_rootf true)       *)
(*   radcan_eq_cond, radcan_eq_cond0, radcan_eq_cond_odd,                     *)
(*   radcan_eq_cond_neg, radcan_eq_cond_real == the decision theorems         *)
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

Module RadcanF (Import N : NUM).

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

(* Roots of expressions *)

(* proot n c, c a positive rational *)
Definition num_root (n : positive) (c : coef) : option (nf * seq cond) :=
  let q := c_to_Q c in
  if Qnum q is Zpos a then
    let: (u, cs) := nf_inv (RRoot n (Qden q)) (nf_root n (Qden q)) in
    Some (nf_mul (nf_root n a) u, cs)
  else None.

Definition root_atom (n : positive) (e : rexpr) : nf :=
  [:: (c_one, ([:: (ARoot n e, 1%N)], [::]))].

Definition nf_prod (l : seq (nf * nat)) : nf :=
  foldr (fun bk acc => nf_mul (nf_pow bk.1 bk.2) acc) nf_one l.

Definition trivial_dec (rem : nf) (l : seq (nf * nat)) : bool :=
  match l with
  | [:: (_, 1%N)] => if const_of rem is Some c then c_eqb c c_one else false
  | _ => false
  end.

(* proot n (c * prod B ^+ k) split over the factors (needs 0 <= B) *)
Definition root_prod (n : positive) (c : coef) (l : seq (nf * nat))
  : option (nf * seq cond) :=
  if num_root n c is Some (q, cs) then
    Some (nf_mul q (nf_prod (map (fun bk => (root_atom n (nf_to_rexpr bk.1),
                                            bk.2)) l)),
          cs ++ map (fun bk => CGe0 (nf_to_rexpr bk.1)) l)
  else None.

(* the same, but proot n (1 * B) stays the atom proot n B, no condition *)
Definition root_split (n : positive) (c : coef) (l : seq (nf * nat))
  : option (nf * seq cond) :=
  if l is [:: (b, 1%N)] then
    if c_eqb c c_one then Some (root_atom n (nf_to_rexpr b), [::])
    else root_prod n c l
  else root_prod n c l.

(* mode MReal, odd n: proot n (c * prod B ^+ k) split without condition *)
Definition root_prod_m (m : rmode) (n : positive) (c : coef)
  (l : seq (nf * nat)) : option (nf * seq cond) :=
  if real_mode m && odd (Pos.to_nat n) then
    if num_root n c is Some (q, cs) then
      Some (nf_mul q (nf_prod (map (fun bk => (root_atom n (nf_to_rexpr bk.1),
                                              bk.2)) l)), cs)
    else None
  else root_prod n c l.

Definition root_split_m (m : rmode) (n : positive) (c : coef)
  (l : seq (nf * nat)) : option (nf * seq cond) :=
  if l is [:: (b, 1%N)] then
    if c_eqb c c_one then Some (root_atom n (nf_to_rexpr b), [::])
    else root_prod_m m n c l
  else root_prod_m m n c l.

(* mode MRealA: |B| is the atom proot 2 (B ^+ 2); under an even root a     *)
(* factor B ^+ k with k even is read as |B| ^+ k (no condition)             *)
Definition abs_nf (b : nf) : nf := root_atom 2 (RPow (nf_to_rexpr b) 2).

Definition absify (m : rmode) (n : positive) (l : seq (nf * nat)) :
  seq (nf * nat) :=
  if abs_mode m && ~~ odd (Pos.to_nat n) then
    map (fun bk => if odd bk.2 then bk else (abs_nf bk.1, bk.2)) l
  else l.

(* c * prod B^k with c < 0 becomes (-c) * (-B1)^k1 * prod B^k, B1 the first
   factor with an odd exponent such that P B1 *)
Fixpoint flip_odd_gen (P : nf -> bool) (l : seq (nf * nat)) :
  option (seq (nf * nat)) :=
  match l with
  | [::] => None
  | (b, k) :: l' =>
    if odd k && P b then Some ((nf_opp b, k) :: l')
    else if flip_odd_gen P l' is Some l'' then Some ((b, k) :: l'') else None
  end.

(* a basis element B with -B in the hints hs is flipped first *)
Definition flip_odd (hs : seq nf) (l : seq (nf * nat)) :
  option (seq (nf * nat)) :=
  if flip_odd_gen (fun b => has (fun h => nf_eqb h (nf_opp b)) hs) l
    is Some l' then Some l'
  else flip_odd_gen (fun _ => true) l.

Definition omega_nf (n : positive) : nf := root_atom n omega_c.

(* proot n e0, p the normal form of e0 *)
Definition nf_rootE (m : rmode) (hs : seq nf) (bs : seq nf) (n : positive)
  (e0 : rexpr) (p : nf) : nf * seq cond :=
  let giveup := (root_atom n (if nf_wf p then nf_to_rexpr p else e0), [::]) in
  let oddn := odd_mode m && odd (Pos.to_nat n) in
  if p is [::] then ([::], [::]) else
  if const_of p is Some c then
    (if num_root n c is Some res then res else
     if oddn then
       (if num_root n (c_opp c) is Some (q, cs) then (nf_opp q, cs)
        else giveup)
     else if neg_mode m then
       (if num_root n (c_opp c) is Some (q, cs) then (nf_mul q (omega_nf n), cs)
        else giveup)
     else giveup) else
  let: (rem, l) := decompose bs p in
  if nilp l then giveup else
  if const_of rem is Some c then
    if nf_eqb p (nf_mul rem (nf_prod l)) && all (fun bk => nf_wf bk.1) l then
      if c_neg c then
        if oddn then
          (if root_split_m m n (c_opp c) l is Some (q, cs) then (nf_opp q, cs)
           else giveup)
        else if (if negw_mode m then None else flip_odd hs l) is Some l' then
          (if root_split_m m n (c_opp c) (absify m n l') is Some res then res
           else giveup)
        else if neg_mode m then
          (if root_prod n (c_opp c) l is Some (q, cs)
           then (nf_mul q (omega_nf n), cs) else giveup)
        else giveup
      else if trivial_dec rem l then giveup
      else if root_prod_m m n c (absify m n l) is Some res then res
      else giveup
    else giveup
  else giveup.

(* mode MNeg: the omega atoms of a single term are inverted directly,
   omega_n ^- k = (-1) ^+ k * omega_n ^+ (k * (n - 1)) *)
Fixpoint vsplit_omega (v : vmono) : seq (positive * nat) * vmono :=
  match v with
  | [::] => ([::], [::])
  | (a, k) :: v' =>
    let: (o, w) := vsplit_omega v' in
    if a is ARoot n e then
      if is_omega e then ((n, k) :: o, w) else (o, (a, k) :: w)
    else (o, (a, k) :: w)
  end.

Definition omega_inv (o : seq (positive * nat)) : nf :=
  foldr (fun nk acc =>
           nf_mul (nf_mul (nf_pow (nf_opp nf_one) nk.2)
                          [:: (c_one, (vsingle (ARoot nk.1 omega_c)
                                         (nk.2 * (Pos.to_nat nk.1).-1),
                                       [::]))]) acc)
        nf_one o.

Definition nf_inv_m (m : rmode) (e0 : rexpr) (p : nf) : nf * seq cond :=
  if neg_mode m then
    if p is [:: (c, (v, mm))] then
      let: (o, w) := vsplit_omega v in
      if o is [::] then nf_inv e0 p else
      let d := [:: (c, (w, mm))] in
      if nf_wf d then
        let: (q, cs) := nf_inv (nf_to_rexpr d) d in (nf_mul q (omega_inv o), cs)
      else nf_inv e0 p
    else nf_inv e0 p
  else nf_inv e0 p.

(* M11: a denominator with several terms, variables and roots *)
Definition rat_mixed (p : nf) : bool :=
  [&& (1 < size p)%N, ~~ novar p &
      has (fun t => ~~ nilp t.2.2 ||
                    has (fun ak => if ak.1 is ARoot _ _ then true else false)
                        t.2.1) p].

(* the inverse, rationalised (checked by nf_simp m) when rt holds *)
Definition nf_inv_r (rt : bool) (m : rmode) (e0 : rexpr) (p : nf) :
  nf * seq cond :=
  if rt && rat_mixed p then
    if nf_inv_rat (nf_simp m) p is Some res then res else nf_inv_m m e0 p
  else nf_inv_m m e0 p.

(* The normaliser *)

Fixpoint normcr (rt : bool) (m : rmode) (hs : seq nf) (bs : seq nf)
  (e : rexpr) : nf * seq cond :=
  match e with
  | RCst z => (nf_single (c_of_Z z) ([::], [::]), [::])
  | RVar i => ([:: (c_one, ([:: (AVar i, 1%N)], [::]))], [::])
  | RRoot n p => (nf_root n p, [::])
  | RRootE n e1 =>
    let: (p, c1) := normcr rt m hs bs e1 in
    let: (q, c2) := nf_rootE m hs bs n e1 p in
    let: (s, c3) := nf_simp m q in (s, c1 ++ c2 ++ c3)
  | RAdd e1 e2 =>
    let: (p1, c1) := normcr rt m hs bs e1 in
    let: (p2, c2) := normcr rt m hs bs e2 in
    let: (s, c3) := nf_simp m (nf_add p1 p2) in (s, c1 ++ c2 ++ c3)
  | ROpp e1 => let: (p, c) := normcr rt m hs bs e1 in (nf_opp p, c)
  | RSub e1 e2 =>
    let: (p1, c1) := normcr rt m hs bs e1 in
    let: (p2, c2) := normcr rt m hs bs e2 in
    let: (s, c3) := nf_simp m (nf_add p1 (nf_opp p2)) in (s, c1 ++ c2 ++ c3)
  | RMul e1 e2 =>
    let: (p1, c1) := normcr rt m hs bs e1 in
    let: (p2, c2) := normcr rt m hs bs e2 in
    let: (s, c3) := nf_simp m (nf_mul p1 p2) in (s, c1 ++ c2 ++ c3)
  | RPow e1 k =>
    let: (p, c1) := normcr rt m hs bs e1 in
    let: (s, c3) := nf_simp m (nf_pow p k) in (s, c1 ++ c3)
  | RInv e1 =>
    let: (p, c1) := normcr rt m hs bs e1 in
    let: (q, c2) := nf_inv_r rt m e1 p in
    let: (s, c3) := nf_simp m q in (s, c1 ++ c2 ++ c3)
  end.

Definition normc := normcr false.

(* normal forms of both sides, with the side conditions used *)
(* nested radicands: a radicand containing roots whose normal form is a
   polynomial without root atom adds its square-free factors to the basis *)
Definition root_free (p : nf) : bool :=
  ispoly p &&
  all (fun t => all (fun ak => if ak.1 is ARoot _ _ then false else true)
                    t.2.1) p.

Definition nested_polys (rt : bool) (m : rmode) (hs bs : seq nf)
  (es : seq rexpr) : seq nf :=
  foldr (fun a acc => if no_root a then acc else
                      let p := (normcr rt m hs bs a).1 in
                      if root_free p then p :: acc else acc)
        [::] (flatten (map radicands es)).

Definition mk_basis_n (rt : bool) (m : rmode) (hs : seq nf)
  (es : seq rexpr) : seq nf :=
  let bs := mk_basis es in
  let ps := nested_polys rt m hs bs es in
  foldl (fun bs p =>
           foldl (fun bs a => pb_insert 64 (pnormal a) bs) bs (sqf 16 p))
        bs ps.

(* mode MReal: conditions 0 <= e with e syntactically nonnegative on a real
   field (even powers, roots of such, positive constants) are dropped *)
Fixpoint nonneg_syn (e : rexpr) : bool :=
  match e with
  | RCst z => Z.leb 0 z
  | RRoot _ _ => true
  | RRootE _ a | RInv a => nonneg_syn a
  | RPow a k => ~~ odd k || nonneg_syn a
  | RAdd a b | RMul a b => nonneg_syn a && nonneg_syn b
  | _ => false
  end.

Definition cfilter (m : rmode) (cs : seq cond) : seq cond :=
  if real_mode m then
    filter (fun c => if c is CGe0 e then ~~ nonneg_syn e else true) cs
  else cs.

Definition radcan_nfb (rt : bool) (m : rmode) (hs bs : seq nf)
  (e1 e2 : rexpr) : nf * nf * seq cond :=
  let: (p1, c1) := normcr rt m hs bs e1 in
  let: (p2, c2) := normcr rt m hs bs e2 in
  (p1, p2, cfilter m (cdedup (c1 ++ c2))).

Definition radcan_nfr (rt : bool) (m : rmode) (e1 e2 : rexpr) :
  nf * nf * seq cond :=
  let hs := neg_hints [:: e1; e2] in
  radcan_nfb rt m hs (mk_basis_n rt m hs [:: e1; e2]) e1 e2.

Definition radcan_nf := radcan_nfr false.

Definition radcan_check_bs (rt : bool) (m : rmode) (hs bs : seq nf)
  (e1 e2 : rexpr) : option (seq cond) :=
  let: (p1, p2, cs) := radcan_nfb rt m hs bs e1 e2 in
  if nf_eqb p1 p2 then Some cs else None.

Definition radcan_check_rt (rt : bool) (m : rmode) (e1 e2 : rexpr) :
  option (seq cond) :=
  let hs := neg_hints [:: e1; e2] in
  radcan_check_bs rt m hs (mk_basis_n rt m hs [:: e1; e2]) e1 e2.

(* M16: the basis refined by irreducible factors (form 1); None when no   *)
(* element splits.  Splitting strengthens the conditions (0 <= x - 1,     *)
(* 0 <= x + 1 instead of 0 <= x ^ 2 - 1): used only as a fallback         *)
Definition radcan_check_irr (rt : bool) (m : rmode) (e1 e2 : rexpr) :
  option (seq cond) :=
  let hs := neg_hints [:: e1; e2] in
  let bs := mk_basis_n rt m hs [:: e1; e2] in
  let bs' := irr_basis bs in
  if size bs' == size bs then None else radcan_check_bs rt m hs bs' e1 e2.

(* M11: mixed denominators are rationalised only when the plain normal      *)
(* forms differ; fa: irreducible basis (M16)                                 *)
Definition radcan_check_rawf (fa : bool) (m : rmode) (e1 e2 : rexpr) :
  option (seq cond) :=
  if fa then
    if radcan_check_irr false m e1 e2 is Some cs then Some cs
    else radcan_check_irr true m e1 e2
  else if radcan_check_rt false m e1 e2 is Some cs then Some cs
  else radcan_check_rt true m e1 e2.

Definition radcan_check_raw := radcan_check_rawf false.

(* Constant radicands over a common coprime basis: every RRoot n p of the
   goal becomes prod_i RRoot n b_i ^ k_i (product checked), b_i small primes
   or elements of the coprime basis of the goal *)

(* a root-free constant expression with a positive integer value *)
Definition const_pos (a : rexpr) : option positive :=
  if const_of (pnorm0 a) is Some c then
    let q := c_to_Q c in
    if p_eqb (Qden q) xH then (if Qnum q is Zpos p then Some p else None)
    else None
  else None.

(* a root-free constant expression with a negative integer value - p *)
Definition const_neg (a : rexpr) : option positive :=
  if const_of (pnorm0 a) is Some c then
    let q := c_to_Q c in
    if p_eqb (Qden q) xH then (if Qnum q is Zneg p then Some p else None)
    else None
  else None.

(* the radicand of RRootE n a read as - p (mode MOdd with n odd, MNeg) *)
Definition odd_neg (m : rmode) (n : positive) (a : rexpr) : option positive :=
  if odd_mode m then (if odd (Pos.to_nat n) then const_neg a else None)
  else if neg_mode m then const_neg a else None.

Fixpoint rconsts (m : rmode) (e : rexpr) : seq positive :=
  match e with
  | RRoot _ p => [:: p]
  | RRootE n a => if const_pos a is Some p then [:: p] else
                  if odd_neg m n a is Some p then [:: p] else rconsts m a
  | ROpp a | RPow a _ | RInv a => rconsts m a
  | RAdd a b | RSub a b | RMul a b => rconsts m a ++ rconsts m b
  | RCst _ | RVar _ => [::]
  end.

Definition root_pows (n : positive) (l : seq (positive * nat)) : rexpr :=
  rprod (map (fun bk => RPow (RRoot n bk.1) bk.2) l).

Definition rw_root (cb : seq int) (n p : positive) : rexpr :=
  let l := cb_factor cb p in
  if i_eqb (fprod l) (i_of_pos p) then root_pows n l else RRoot n p.

(* proot n (- p): - proot n p (MOdd, n odd), proot n p * omega_n (MNeg) *)
Definition neg_root (m : rmode) (cb : seq int) (n p : positive) : rexpr :=
  if neg_mode m then RMul (rw_root cb n p) (RRootE n omega_c)
  else ROpp (rw_root cb n p).

Fixpoint cb_rw (m : rmode) (cb : seq int) (e : rexpr) : rexpr :=
  match e with
  | RRoot n p => rw_root cb n p
  | RRootE n a => if const_pos a is Some p then rw_root cb n p else
                  if odd_neg m n a is Some p then neg_root m cb n p else
                  RRootE n (cb_rw m cb a)
  | RAdd a b => RAdd (cb_rw m cb a) (cb_rw m cb b)
  | ROpp a => ROpp (cb_rw m cb a)
  | RSub a b => RSub (cb_rw m cb a) (cb_rw m cb b)
  | RMul a b => RMul (cb_rw m cb a) (cb_rw m cb b)
  | RPow a k => RPow (cb_rw m cb a) k
  | RInv a => RInv (cb_rw m cb a)
  | RCst _ | RVar _ => e
  end.

Definition radcan_check_rootf (fa : bool) (m : rmode) (e1 e2 : rexpr) :
  option (seq cond) :=
  let cb := const_basis (rconsts m e1 ++ rconsts m e2) in
  radcan_check_rawf fa m (cb_rw m cb e1) (cb_rw m cb e2).

Definition radcan_check_root := radcan_check_rootf false.

(* Root-free normaliser: sound for any root function *)

Definition cancel_one0 (p : nf) (e : rexpr) : option (nf * cond) :=
  let: (P, R) := split_inv (AInv e) p in
  let D := pnorm0 e in
  if P is [::] then None else
  if pdiv P D is Some Qt then
    if nf_eqb P (nf_mul0 Qt D) then Some (nf_add Qt R, CNeq0 e) else None
  else if gcd_split P D is Some (G, P', D') then
    if nf_eqb P (nf_mul0 P' G) && nf_eqb D (nf_mul0 D' G) then
      Some (nf_add (nf_mul0 P' (nf_inv0 D')) R, CNeq0 (nf_to_rexpr0 G))
    else None
  else None.

Definition nf_cancel0 (p : nf) : nf * seq cond :=
  foldl (fun acc e => if cancel_one0 acc.1 e is Some (q, c)
                      then (q, rcons acc.2 c) else acc)
        (p, [::]) (inv_atoms p).

Fixpoint normc0 (e : rexpr) : nf * seq cond :=
  match e with
  | RCst z => (nf_single (c_of_Z z) ([::], [::]), [::])
  | RVar i => (atom_nf (AVar i), [::])
  | RRoot n p => (atom_nf (ARoot n (RCst (Zpos p))), [::])
  | RRootE n e1 =>
    let: (p, c1) := normc0 e1 in (atom_nf (ARoot n (nf_to_rexpr0 p)), c1)
  | RAdd e1 e2 =>
    let: (p1, c1) := normc0 e1 in let: (p2, c2) := normc0 e2 in
    let: (s, c3) := nf_cancel0 (nf_add p1 p2) in (s, c1 ++ c2 ++ c3)
  | ROpp e1 => let: (p, c) := normc0 e1 in (nf_opp p, c)
  | RSub e1 e2 =>
    let: (p1, c1) := normc0 e1 in let: (p2, c2) := normc0 e2 in
    let: (s, c3) := nf_cancel0 (nf_add p1 (nf_opp p2)) in (s, c1 ++ c2 ++ c3)
  | RMul e1 e2 =>
    let: (p1, c1) := normc0 e1 in let: (p2, c2) := normc0 e2 in
    let: (s, c3) := nf_cancel0 (nf_mul0 p1 p2) in (s, c1 ++ c2 ++ c3)
  | RPow e1 k =>
    let: (p, c1) := normc0 e1 in
    let: (s, c3) := nf_cancel0 (nf_pow0 p k) in (s, c1 ++ c3)
  | RInv e1 =>
    let: (p, c1) := normc0 e1 in
    let: (s, c3) := nf_cancel0 (nf_inv0 p) in (s, c1 ++ c3)
  end.

Definition radcan_check0 (e1 e2 : rexpr) : option (seq cond) :=
  let: (p1, c1) := normc0 e1 in
  let: (p2, c2) := normc0 e2 in
  if nf_eqb p1 p2 then Some (cdedup (c1 ++ c2)) else None.

(* the checkers: any posroot, with an oddroot, with a negroot; the    *)
(* irreducible basis (M16) is tried last                                *)
Definition radcan_check (e1 e2 : rexpr) : option (seq cond) :=
  if no_root e1 && no_root e2 then radcan_check0 e1 e2
  else if radcan_check_root MStd e1 e2 is Some cs then Some cs
  else radcan_check_rootf true MStd e1 e2.

Definition radcan_check_odd (e1 e2 : rexpr) : option (seq cond) :=
  if no_root e1 && no_root e2 then radcan_check0 e1 e2
  else if radcan_check_root MOdd e1 e2 is Some cs then Some cs
  else radcan_check_rootf true MOdd e1 e2.

(* MNegW (omega_n preferred to a flipped base) only when MNeg fails *)
Definition radcan_check_neg (e1 e2 : rexpr) : option (seq cond) :=
  if no_root e1 && no_root e2 then radcan_check0 e1 e2
  else if radcan_check_root MNeg e1 e2 is Some cs then Some cs
  else if radcan_check_root MNegW e1 e2 is Some cs then Some cs
  else if radcan_check_rootf true MNeg e1 e2 is Some cs then Some cs
  else radcan_check_rootf true MNegW e1 e2.

(* real fields: absolute values first (MRealA), then MReal *)
Definition radcan_check_real (e1 e2 : rexpr) : option (seq cond) :=
  if no_root e1 && no_root e2 then radcan_check0 e1 e2
  else if radcan_check_root MRealA e1 e2 is Some cs then Some cs
  else if radcan_check_root MReal e1 e2 is Some cs then Some cs
  else if radcan_check_rootf true MRealA e1 e2 is Some cs then Some cs
  else radcan_check_rootf true MReal e1 e2.

Lemma ocase_some (T : Type) (a b : option T) x :
  (if a is Some y then Some y else b) = Some x -> a = Some x \/ b = Some x.
Proof. by case: a => [y [->]|]; [left | right]. Qed.
Arguments ocase_some {T a b x}.

Local Open Scope ring_scope.

Section CondSound.

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

(* roots of expressions *)

Lemma const_of_sound p c : const_of p = Some c -> nf_interp p = C2F c.
Proof.
case: p => [[<-]|[c' [[|??] [|??]]] [|??]] //=.
  by rewrite nf_interp_nil C2F_c_zero.
move=> [<-]; rewrite nf_interp_cons nf_interp_nil /key_interp /=.
by rewrite vmono_interp_nil mono_interp_nil !mulr1 addr0.
Qed.

Lemma num_root_sound n c res : num_root n c = Some res -> holds res.2 ->
  0 <= C2F (F:=F) c /\ nf_interp res.1 = proot r (Pos.to_nat n) (C2F c).
Proof.
have N0 : (0 < Pos.to_nat n)%N by apply/ssrnat.ltP; exact: Pos2Nat.is_pos.
rewrite /num_root /C2F; case: (c_to_Q c) => [[|a|a] d] //=.
have := @nf_inv_sound F r env (RRoot n d) (nf_root n d)
  (esym (nf_root_sound r env n d)).
case: nf_inv => u cs /= Hu [<-] /= /Hu {}Hu.
have d0 : 0 <= (pos2F F d)^-1 by rewrite invr_ge0 pos2F_ge0.
split; first by rewrite /Q2F /= divr_ge0 ?pos2F_ge0.
rewrite nf_mul_sound Hu !nf_root_sound /Q2F /= prootM ?pos2F_ge0 //.
by rewrite prootV ?pos2F_ge0.
Qed.

Lemma nf_prod_sound l :
  nf_interp (nf_prod l) = \prod_(bk <- l) nf_interp bk.1 ^+ bk.2.
Proof.
elim: l => [|bk l IH] /=; first by rewrite big_nil nf_one_sound.
by rewrite big_cons nf_mul_sound nf_pow_sound IH.
Qed.

Lemma proot_prod n c l : (0 < n)%N -> 0 <= c ->
  (forall bk, List.In bk l -> 0 <= nf_interp bk.1) ->
  proot r n (c * \prod_(bk <- l) nf_interp bk.1 ^+ bk.2) =
  proot r n c * \prod_(bk <- l) proot r n (nf_interp bk.1) ^+ bk.2.
Proof.
move=> n0 c0; elim: l c c0 => [|bk l IH] c c0 Hl.
  by rewrite !big_nil !mulr1.
have b0 : 0 <= nf_interp bk.1 by apply: Hl; left.
have Hl' : forall bk', List.In bk' l -> 0 <= nf_interp bk'.1.
  by move=> bk' H; apply: Hl; right.
rewrite !big_cons mulrA (mulrA c) IH ?mulr_ge0 ?exprn_ge0 //.
by rewrite prootM ?exprn_ge0 // prootX.
Qed.

Lemma all_In (T : Type) (P : pred T) l x : all P l -> List.In x l -> P x.
Proof. by elim: l => [|y l IH] //= /andP[Py Pl] [<-|/IH]; [|apply]. Qed.

Lemma root_atoms_prod n l : (forall bk, List.In bk l -> nf_wf bk.1) ->
  \prod_(bk <- l) nf_interp (root_atom n (nf_to_rexpr bk.1)) ^+ bk.2 =
  \prod_(bk <- l) proot r (Pos.to_nat n) (nf_interp bk.1) ^+ bk.2.
Proof.
elim: l => [|bk l IH] Hw; first by rewrite !big_nil.
rewrite !big_cons IH; last by move=> bk' H; apply: Hw; right.
by rewrite /root_atom nf_atom1 /= nf_to_rexpr_sound //; apply: Hw; left.
Qed.

Lemma root_prod_sound n c l res : root_prod n c l = Some res -> holds res.2 ->
  all (fun bk => nf_wf bk.1) l ->
  nf_interp res.1 =
  proot r (Pos.to_nat n) (C2F c * \prod_(bk <- l) nf_interp bk.1 ^+ bk.2).
Proof.
have N0 : (0 < Pos.to_nat n)%N by apply/ssrnat.ltP; exact: Pos2Nat.is_pos.
rewrite /root_prod; case En : (num_root n c) => [[q cs]|] // [<-] /=.
case/holds_cat => /(num_root_sound En) [c0 Hq] Hl Hwf.
have Hw : forall bk, List.In bk l -> nf_wf bk.1 by move=> bk; apply: all_In Hwf.
have Hb : forall bk, List.In bk l -> 0 <= nf_interp bk.1.
  move=> bk Hbk; have := Hl (CGe0 (nf_to_rexpr bk.1)).
  rewrite /= nf_to_rexpr_sound ?Hw //; apply.
  by apply/List.in_map_iff; exists bk.
rewrite nf_mul_sound Hq proot_prod // nf_prod_sound big_map.
by rewrite root_atoms_prod.
Qed.

Lemma root_split_sound n c l res : root_split n c l = Some res -> holds res.2 ->
  all (fun bk => nf_wf bk.1) l ->
  nf_interp res.1 =
  proot r (Pos.to_nat n) (C2F c * \prod_(bk <- l) nf_interp bk.1 ^+ bk.2).
Proof.
rewrite /root_split.
case: l => [|[b [|[|k]]] [|bk l]]; try exact: root_prod_sound.
case: ifP => [/(@c_eqbP F _ _) Hc [<-] _ /andP[wb _]|_]; last first.
  exact: root_prod_sound.
rewrite /root_atom nf_atom1 /= nf_to_rexpr_sound // Hc C2F_c_one mul1r.
by rewrite big_seq1 expr1.
Qed.

Lemma flip_odd_gen_sound P l l' : flip_odd_gen P l = Some l' ->
  \prod_(bk <- l') nf_interp bk.1 ^+ bk.2 =
    - \prod_(bk <- l) nf_interp bk.1 ^+ bk.2 /\
  (all (fun bk => nf_wf bk.1) l -> all (fun bk => nf_wf bk.1) l').
Proof.
elim: l l' => [|[b k] l IH] l' //=.
case: ifP => [/andP[Ok _] [<-]|_].
  rewrite !big_cons /= nf_opp_sound exprNn -signr_odd Ok expr1 mulN1r mulNr.
  split=> // /andP[wb ->]; rewrite andbT.
  by move: wb; rewrite /nf_wf /nf_opp all_map.
case E : (flip_odd_gen P l) => [l''|] // [<-].
have [H1 H2] := IH _ E.
rewrite !big_cons H1 mulrN; split=> //=.
by case/andP => -> /H2.
Qed.

Lemma flip_odd_sound hs l l' : flip_odd hs l = Some l' ->
  \prod_(bk <- l') nf_interp bk.1 ^+ bk.2 =
    - \prod_(bk <- l) nf_interp bk.1 ^+ bk.2 /\
  (all (fun bk => nf_wf bk.1) l -> all (fun bk => nf_wf bk.1) l').
Proof.
rewrite /flip_odd; case E : flip_odd_gen => [l1|]; last first.
  exact: flip_odd_gen_sound.
by move=> [<-]; apply: flip_odd_gen_sound E.
Qed.

Lemma root_prod_ge0 n c l res : root_prod n c l = Some res -> holds res.2 ->
  all (fun bk => nf_wf bk.1) l ->
  0 <= C2F c * \prod_(bk <- l) nf_interp bk.1 ^+ bk.2.
Proof.
rewrite /root_prod; case En : (num_root n c) => [[q cs]|] // [<-] /=.
case/holds_cat => /(num_root_sound En) [c0 _] Hl Hwf.
rewrite mulr_ge0 //; elim: l Hl Hwf {En} => [|bk l IH] Hl Hwf.
  by rewrite big_nil.
case/andP: Hwf => wb Hwf.
rewrite big_cons mulr_ge0 ?exprn_ge0 //; last first.
  by apply: IH => // c' Hc'; apply: Hl; right.
have := Hl (CGe0 (nf_to_rexpr bk.1)); rewrite /= nf_to_rexpr_sound //.
by apply; left.
Qed.

Lemma proot_prod_odd (rl : realroot r) N (l : seq (nf * nat)) : odd N ->
  proot r N (\prod_(bk <- l) nf_interp bk.1 ^+ bk.2) =
  \prod_(bk <- l) proot r N (nf_interp bk.1) ^+ bk.2.
Proof.
move=> ON; have N0 : (0 < N)%N by case: N ON.
elim: l => [|bk l IH]; first by rewrite !big_nil proot_1.
by rewrite !big_cons (proot_oddM rl) // (proot_oddX rl) // IH.
Qed.

Lemma root_prod_m_sound n c l res : root_prod_m mo n c l = Some res ->
  holds res.2 -> all (fun bk => nf_wf bk.1) l ->
  nf_interp res.1 =
  proot r (Pos.to_nat n) (C2F c * \prod_(bk <- l) nf_interp bk.1 ^+ bk.2).
Proof.
rewrite /root_prod_m; case: ifP => [/andP[Hm On]|_]; last first.
  exact: root_prod_sound.
case En : (num_root n c) => [[q cs]|] // [<-] /= /(num_root_sound En) [c0 Hq].
move=> Hwf.
have Hw : forall bk, List.In bk l -> nf_wf bk.1 by move=> bk; apply: all_In Hwf.
rewrite nf_mul_sound Hq nf_prod_sound big_map root_atoms_prod //.
by rewrite (proot_oddM (Hrl Hm)) // (proot_prod_odd (Hrl Hm)).
Qed.

Lemma root_split_m_sound n c l res : root_split_m mo n c l = Some res ->
  holds res.2 -> all (fun bk => nf_wf bk.1) l ->
  nf_interp res.1 =
  proot r (Pos.to_nat n) (C2F c * \prod_(bk <- l) nf_interp bk.1 ^+ bk.2).
Proof.
rewrite /root_split_m.
case: l => [|[b [|[|k]]] [|bk l]]; try exact: root_prod_m_sound.
case: ifP => [/(@c_eqbP F _ _) Hc [<-] _ /andP[wb _]|_]; last first.
  exact: root_prod_m_sound.
rewrite /root_atom nf_atom1 /= nf_to_rexpr_sound // Hc C2F_c_one mul1r.
by rewrite big_seq1 expr1.
Qed.

Lemma absify_sound n l : all (fun bk => nf_wf bk.1) l ->
  \prod_(bk <- absify mo n l) nf_interp bk.1 ^+ bk.2 =
    \prod_(bk <- l) nf_interp bk.1 ^+ bk.2 /\
  all (fun bk => nf_wf bk.1) (absify mo n l).
Proof.
rewrite /absify; case: ifP => [/andP[Hm _]|_] Hwf //; split; last first.
  elim: (l) Hwf => //= -[b k] l' IH /andP[wb /IH ->].
  by case: ifP; rewrite /= ?wb.
have Hr : real_mode mo by case: (mo) Hm.
elim: l Hwf => [|[b k] l IH] /=; first by rewrite !big_nil.
case/andP => /= wb /IH {}IH; rewrite !big_cons IH; congr (_ * _).
case: ifP => //= Ek.
rewrite /abs_nf /root_atom nf_atom1 /= nf_to_rexpr_sound //.
rewrite (proot_sqr (Hrl Hr)) -(odd_double_half k) Ek add0n.
by rewrite -mul2n !exprM real_normK // (realroot_real (Hrl Hr)).
Qed.

Lemma nf_rootE_sound hs bs n e0 p : rinterp r env e0 = nf_interp p ->
  holds (nf_rootE mo hs bs n e0 p).2 ->
  nf_interp (nf_rootE mo hs bs n e0 p).1 = proot r (Pos.to_nat n) (nf_interp p).
Proof.
move=> He.
have N0 : (0 < Pos.to_nat n)%N by apply/ssrnat.ltP; exact: Pos2Nat.is_pos.
have Hg : nf_interp (root_atom n (if nf_wf p then nf_to_rexpr p else e0)) =
          proot r (Pos.to_nat n) (nf_interp p).
  rewrite /root_atom nf_atom1 /=.
  by case: ifP => [/nf_to_rexpr_sound -> | _]; rewrite ?He.
have HN : odd_mode mo && odd (Pos.to_nat n) -> forall a,
    proot r (Pos.to_nat n) a = - proot r (Pos.to_nat n) (- a).
  by case/andP => /Ho Hor On a; rewrite (prootN Hor) // opprK.
have HW : neg_mode mo -> forall a, 0 <= a ->
    proot r (Pos.to_nat n) (- a) =
    proot r (Pos.to_nat n) a * nf_interp (omega_nf n).
  move=> /Hng w a a0.
  by rewrite /omega_nf /root_atom nf_atom1 /= pos2F1 (prootN1 w N0 a0).
rewrite /nf_rootE; case: p He Hg => [|t p'] He Hg.
  by rewrite /= nf_interp_nil proot_0.
set p := t :: p'.
case Ec : (const_of p) => [c|].
  case En : (num_root n c) => [res|].
    by move=> /(num_root_sound En) [_ ->]; rewrite (const_of_sound Ec).
  case: ifP => [On|_].
    case En' : (num_root n (c_opp c)) => [[q cs]|] //=.
    move=> /(num_root_sound En') /= [_ Hq].
    by rewrite nf_opp_sound Hq (const_of_sound Ec) [RHS](HN On) C2F_c_opp.
  case: ifP => [Hm|_ //].
  case En' : (num_root n (c_opp c)) => [[q cs]|] //=.
  move=> /(num_root_sound En') /= [c0 Hq].
  by rewrite nf_mul_sound Hq -(HW Hm _ c0) (const_of_sound Ec) C2F_c_opp opprK.
case: (decompose bs p) => rem l.
case: ifP => _ //.
case Er : (const_of rem) => [c|] //.
case: ifP => [/andP[/nf_eqb_eq Hp Hwf]|_] //.
have Hpc : nf_interp p = C2F c * \prod_(bk <- l) nf_interp bk.1 ^+ bk.2.
  by rewrite Hp nf_mul_sound (const_of_sound Er) nf_prod_sound.
case: ifP => _.
  case: ifP => [On|_].
    case Es : (root_split_m mo n (c_opp c) l) => [[q cs]|] //= Hh.
    rewrite nf_opp_sound (root_split_m_sound Es Hh Hwf) Hpc [RHS](HN On).
    by rewrite C2F_c_opp mulNr.
  case Ef : (if negw_mode mo then None else flip_odd hs l) => [l'|].
    have Ef' : flip_odd hs l = Some l' by move: Ef; case: ifP.
    have [Hl' Hw'] := flip_odd_sound Ef'.
    have [Ha Hwa] := absify_sound n (Hw' Hwf).
    case Es : (root_split_m mo n (c_opp c) (absify mo n l')) => [res|] // Hh.
    rewrite (root_split_m_sound Es Hh Hwa) Ha Hpc Hl' C2F_c_opp.
    by rewrite mulrNN.
  case: ifP => [Hm|_ //].
  case Es : (root_prod n (c_opp c) l) => [[q cs]|] //= Hh.
  rewrite nf_mul_sound (root_prod_sound Es Hh Hwf).
  rewrite -HW ?(root_prod_ge0 Es Hh Hwf) //.
  by rewrite Hpc C2F_c_opp mulNr opprK.
case: ifP => _ //.
have [Ha Hwa] := absify_sound n Hwf.
case Es : (root_prod_m mo n c (absify mo n l)) => [res|] // Hh.
by rewrite (root_prod_m_sound Es Hh Hwa) Ha Hpc.
Qed.

(* inverses of omega atoms (mode MNeg) *)

Lemma vsplit_omega_sound v :
  vmono_interp v = vmono_interp (vsplit_omega v).2 *
    \prod_(nk <- (vsplit_omega v).1) proot r (Pos.to_nat nk.1) (-1) ^+ nk.2.
Proof.
elim: v => [|[a k] v IH] /=; first by rewrite vmono_interp_nil big_nil mulr1.
case: (vsplit_omega v) IH => o w /= IH.
have Hd : vmono_interp ((a, k) :: v) = vmono_interp ((a, k) :: w) *
    \prod_(nk <- o) proot r (Pos.to_nat nk.1) (-1) ^+ nk.2.
  by rewrite !vmono_interp_cons IH mulrA.
case: a Hd => [i|e|n e] Hd //; case: ifP => [/is_omegaP -> |_] //.
by rewrite vmono_interp_cons IH big_cons /= pos2F1 mulrCA.
Qed.

Lemma omega_inv_sound (w : negroot r) o :
  nf_interp (omega_inv o) =
    (\prod_(nk <- o) proot r (Pos.to_nat nk.1) (-1) ^+ nk.2)^-1.
Proof.
elim: o => [|[n k] o IH] /=; first by rewrite nf_one_sound big_nil invr1.
have N0 : (0 < Pos.to_nat n)%N by apply/ssrnat.ltP; exact: Pos2Nat.is_pos.
rewrite nf_mul_sound IH big_cons invfM /=; congr (_ * _).
rewrite nf_mul_sound nf_pow_sound nf_opp_sound nf_one_sound.
rewrite nf_interp_cons nf_interp_nil addr0 /key_interp /= vsingle_sound /=.
rewrite mono_interp_nil C2F_c_one pos2F1 !mulr1 mul1r.
set x := proot r _ (-1).
have xN : x ^+ Pos.to_nat n = -1 by exact: prootN1K.
have x0 : x != 0.
  apply/eqP => x0; move: xN; rewrite x0 expr0n gtn_eqF // => /eqP.
  by rewrite eq_sym oppr_eq0 oner_eq0.
have Hk : x ^+ (k * (Pos.to_nat n).-1) * x ^+ k = (-1) ^+ k.
  by rewrite -exprD -mulnSr prednK // mulnC exprM xN.
apply: (mulIf (expf_neq0 k x0)); rewrite mulVf ?expf_neq0 // -mulrA Hk.
by rewrite -exprMn mulrNN mulr1 expr1n.
Qed.

Lemma nf_inv_m_sound e0 p :
  rinterp r env e0 = nf_interp p -> holds (nf_inv_m mo e0 p).2 ->
  nf_interp (nf_inv_m mo e0 p).1 = (nf_interp p)^-1.
Proof.
move=> He; rewrite /nf_inv_m; case: ifP => [Hm|_]; last exact: nf_inv_sound He.
have w : negroot r by apply: Hng; case: (mo) Hm.
case: p He => [|[c [v mm]] [|t p]] He;
  [exact: nf_inv_sound He| |exact: nf_inv_sound He].
have := vsplit_omega_sound v; case: (vsplit_omega v) => o vw Hv.
case: o Hv => [|nk o] Hv; first exact: nf_inv_sound He.
case: ifP => [Hwf|_]; last exact: nf_inv_sound He.
have := @nf_inv_sound F r env _ [:: (c, (vw, mm))]
  (nf_to_rexpr_sound r env Hwf).
case: nf_inv => q cs Hq /Hq {}Hq.
rewrite nf_mul_sound Hq (omega_inv_sound w) -invfM.
rewrite !nf_interp_cons !nf_interp_nil !addr0.
by rewrite /key_interp /= Hv /= -!mulrA (mulrC (mono_interp _)).
Qed.

Lemma nf_inv_r_sound rt e0 p :
  rinterp r env e0 = nf_interp p -> holds (nf_inv_r rt mo e0 p).2 ->
  nf_interp (nf_inv_r rt mo e0 p).1 = (nf_interp p)^-1.
Proof.
move=> He; rewrite /nf_inv_r; case: ifP => _; last exact: nf_inv_m_sound.
case E : (nf_inv_rat _ _) => [[q cs]|]; last exact: nf_inv_m_sound.
exact: (nf_inv_rat_sound (@nf_simp_sound) E).
Qed.

(* the normaliser *)

Theorem normcr_sound rt hs bs e : holds (normcr rt mo hs bs e).2 ->
  rinterp r env e = nf_interp (normcr rt mo hs bs e).1.
Proof.
elim: e => [z|i|n p|n e1 IH1|e1 IH1 e2 IH2|e1 IH1|e1 IH1 e2 IH2|e1 IH1 e2 IH2|
            e1 IH1 k|e1 IH1] /=.
- move=> _; rewrite nf_single_sound /key_interp /=.
  by rewrite vmono_interp_nil mono_interp_nil !mulr1 C2F_c_of_Z.
- by move=> _; rewrite nf_atom1.
- by move=> _; rewrite nf_root_sound.
- move: IH1; case: (normcr rt mo hs bs e1) => p c1 /= IH1.
  have := @nf_rootE_sound hs bs n e1 p; case: nf_rootE => q c2 /= Hq.
  have := @nf_simp_sound q; case: nf_simp => s c3 /= Hs.
  case/holds_cat => /IH1 He /holds_cat [/(Hq He) Hq' /Hs ->].
  by rewrite Hq' He.
- move: IH1 IH2; case: (normcr rt mo hs bs e1) => p1 c1.
  case: (normcr rt mo hs bs e2) => p2 c2 /= IH1 IH2.
  have := @nf_simp_sound (nf_add p1 p2); case: nf_simp => s c3 /= Hs.
  case/holds_cat => /IH1 -> /holds_cat [/IH2 -> /Hs ->].
  by rewrite nf_add_sound.
- move: IH1; case: (normcr rt mo hs bs e1) => p c1 /= IH1 /IH1 ->.
  by rewrite nf_opp_sound.
- move: IH1 IH2; case: (normcr rt mo hs bs e1) => p1 c1.
  case: (normcr rt mo hs bs e2) => p2 c2 /= IH1 IH2.
  have := @nf_simp_sound (nf_add p1 (nf_opp p2)); case: nf_simp => s c3 /= Hs.
  case/holds_cat => /IH1 -> /holds_cat [/IH2 -> /Hs ->].
  by rewrite nf_add_sound nf_opp_sound.
- move: IH1 IH2; case: (normcr rt mo hs bs e1) => p1 c1.
  case: (normcr rt mo hs bs e2) => p2 c2 /= IH1 IH2.
  have := @nf_simp_sound (nf_mul p1 p2); case: nf_simp => s c3 /= Hs.
  case/holds_cat => /IH1 -> /holds_cat [/IH2 -> /Hs ->].
  by rewrite nf_mul_sound.
- move: IH1; case: (normcr rt mo hs bs e1) => p c1 /= IH1.
  have := @nf_simp_sound (nf_pow p k); case: nf_simp => s c3 /= Hs.
  case/holds_cat => /IH1 -> /Hs ->.
  by rewrite nf_pow_sound.
move: IH1; case: (normcr rt mo hs bs e1) => p c1 /= IH1.
have := @nf_inv_r_sound rt e1 p; case: nf_inv_r => q c2 /= Hq.
have := @nf_simp_sound q; case: nf_simp => s c3 /= Hs.
case/holds_cat => /IH1 He /holds_cat [/(Hq He) Hq' /Hs ->].
by rewrite Hq' He.
Qed.

Theorem normc_sound hs bs e : holds (normc mo hs bs e).2 ->
  rinterp r env e = nf_interp (normc mo hs bs e).1.
Proof. exact: normcr_sound. Qed.

(* soundness of the checkers in mode mo *)

(* mode MReal: the dropped conditions hold *)

Lemma nonneg_syn_sound (rl : realroot r) e :
  nonneg_syn e -> 0 <= rinterp r env e.
Proof.
elim: e => [[|z|z]|i|n p|n a IHa|a IHa b IHb|a IHa|a IHa b IHb|a IHa b IHb|
            a IHa k|a IHa] //=.
- by rewrite proot_ge0 ?pos2F_ge0 //; apply/ssrnat.ltP; exact: Pos2Nat.is_pos.
- move/IHa => a0; rewrite proot_ge0 //.
  by apply/ssrnat.ltP; exact: Pos2Nat.is_pos.
- by case/andP => /IHa a0 /IHb b0; rewrite addr_ge0.
- by case/andP => /IHa a0 /IHb b0; rewrite mulr_ge0.
- case/orP => [Ek|/IHa a0]; last by rewrite exprn_ge0.
  exact: real_exprn_even_ge0 (realroot_real rl _) Ek.
by move/IHa; rewrite invr_ge0.
Qed.

Lemma cfilter_sound cs : holds (cfilter mo cs) -> holds cs.
Proof.
rewrite /cfilter; case: ifP => // Hm.
elim: cs => [|c cs IH] //= H c' [<-|Hc']; last first.
  by apply: IH Hc' => c'' Hc''; apply: H; case: ifP => _ //; right.
case: c H => [e|e] H.
  case: ifP H => /= [Hn H|Hn _]; first exact: (H _ (or_introl erefl)).
  by apply: (nonneg_syn_sound (Hrl Hm)); rewrite -[nonneg_syn e]negbK Hn.
exact: (H _ (or_introl erefl)).
Qed.

(* any basis: it only guides decompose, whose results are checked *)
Lemma radcan_check_bs_sound rt hs bs e1 e2 cs :
  radcan_check_bs rt mo hs bs e1 e2 = Some cs ->
  all_conds cs -> rinterp r env e1 = rinterp r env e2.
Proof.
rewrite /radcan_check_bs /radcan_nfb.
have := @normcr_sound rt hs bs e1; case: (normcr _ _ _ _ e1) => p1 c1 /= H1.
have := @normcr_sound rt hs bs e2; case: (normcr _ _ _ _ e2) => p2 c2 /= H2.
case: ifP => // /nf_eqb_eq Hp [<-].
move=> /all_condsP /cfilter_sound /holds_dedup /holds_cat [/H1 -> /H2 ->].
by rewrite Hp.
Qed.

Lemma radcan_check_rt_sound rt e1 e2 cs :
  radcan_check_rt rt mo e1 e2 = Some cs ->
  all_conds cs -> rinterp r env e1 = rinterp r env e2.
Proof. exact: radcan_check_bs_sound. Qed.

Lemma radcan_check_irr_sound rt e1 e2 cs :
  radcan_check_irr rt mo e1 e2 = Some cs ->
  all_conds cs -> rinterp r env e1 = rinterp r env e2.
Proof.
by rewrite /radcan_check_irr; case: ifP => // _; exact: radcan_check_bs_sound.
Qed.

Theorem radcan_eq_cond_rawf fa e1 e2 cs :
  radcan_check_rawf fa mo e1 e2 = Some cs ->
  all_conds cs -> rinterp r env e1 = rinterp r env e2.
Proof.
rewrite /radcan_check_rawf; case: fa => /= /ocase_some [] H.
- exact: radcan_check_irr_sound H.
- exact: radcan_check_irr_sound H.
- exact: radcan_check_rt_sound H.
- exact: radcan_check_rt_sound H.
Qed.

Theorem radcan_eq_cond_raw e1 e2 cs : radcan_check_raw mo e1 e2 = Some cs ->
  all_conds cs -> rinterp r env e1 = rinterp r env e2.
Proof. exact: radcan_eq_cond_rawf. Qed.

Lemma proot_prod_pos N l : (0 < N)%N ->
  proot r N (\prod_(bk <- l) pos2F F bk.1 ^+ bk.2) =
  \prod_(bk <- l) proot r N (pos2F F bk.1) ^+ bk.2.
Proof.
move=> N0; elim: l => [|[b k] l IH]; first by rewrite !big_nil proot_1.
rewrite !big_cons prootM ?exprn_ge0 ?pos2F_ge0 //; last first.
  by rewrite prodr_ge0 // => i _; rewrite exprn_ge0 ?pos2F_ge0.
by rewrite IH prootX ?pos2F_ge0.
Qed.

Lemma rw_root_sound cb n p :
  rinterp r env (rw_root cb n p) = proot r (Pos.to_nat n) (pos2F F p).
Proof.
have N0 : (0 < Pos.to_nat n)%N by apply/ssrnat.ltP; exact: Pos2Nat.is_pos.
rewrite /rw_root; case: ifP => [/i_eqbP H|_] //.
rewrite /root_pows rprod_sound big_map.
have -> : pos2F F p = \prod_(bk <- cb_factor cb p) pos2F F bk.1 ^+ bk.2.
  by rewrite -fprod_sound /I2F H /i_of_pos i_of_ZK.
by rewrite proot_prod_pos.
Qed.

Lemma const_of_pnorm0 a c :
  const_of (pnorm0 a) = Some c -> rinterp r env a = C2F c.
Proof.
rewrite (pnorm0_sound (proot r) env a).
move: (pnorm0 a) => q; case: q => [[<-]|[c' [[|??] [|??]]] [|??]] //=.
  by rewrite nf_interp0_nil C2F_c_zero.
move=> [<-]; rewrite nf_interp0_cons nf_interp0_nil vmono_interp0_nil.
by rewrite mulr1 addr0.
Qed.

Lemma const_pos_sound a p : const_pos a = Some p -> rinterp r env a = pos2F F p.
Proof.
rewrite /const_pos; case E : (const_of (pnorm0 a)) => [c|] //.
rewrite (const_of_pnorm0 E).
rewrite /C2F; case: (c_to_Q c) => [[|n|n] d] //=; rewrite /p_eqb.
all: case: d => [d|d|] //= [<-].
by rewrite /Q2F /= pos2F1 divr1.
Qed.

Lemma const_neg_sound a p :
  const_neg a = Some p -> rinterp r env a = - pos2F F p.
Proof.
rewrite /const_neg; case E : (const_of (pnorm0 a)) => [c|] //.
rewrite (const_of_pnorm0 E).
rewrite /C2F; case: (c_to_Q c) => [[|n|n] d] //=; rewrite /p_eqb.
all: case: d => [d|d|] //= [<-].
by rewrite /Q2F /= pos2F1 divr1.
Qed.

Lemma neg_root_sound cb n a p : odd_neg mo n a = Some p ->
  rinterp r env (neg_root mo cb n p) = proot r (Pos.to_nat n) (rinterp r env a).
Proof.
have N0 : (0 < Pos.to_nat n)%N by apply/ssrnat.ltP; exact: Pos2Nat.is_pos.
rewrite /odd_neg /neg_root; case: ifP => [Hm|_].
  have -> : neg_mode mo = false by case: (mo) Hm.
  case: ifP => // On /const_neg_sound ->.
  by rewrite /= rw_root_sound (prootN (Ho Hm)) // opprK.
case: ifP => // Hm /const_neg_sound ->.
by rewrite /= rw_root_sound pos2F1 (prootN1 (Hng Hm) N0 (pos2F_ge0 _)).
Qed.

Lemma cb_rw_sound cb e : rinterp r env (cb_rw mo cb e) = rinterp r env e.
Proof.
elim: e => [z|i|n p|n e1 IH1|e1 IH1 e2 IH2|e1 IH1|e1 IH1 e2 IH2|e1 IH1 e2 IH2|
            e1 IH1 k|e1 IH1] //=; rewrite ?IH1 ?IH2 //.
- exact: rw_root_sound.
case E : (const_pos e1) => [p|] /=.
  by rewrite rw_root_sound (const_pos_sound E).
case E' : (odd_neg mo n e1) => [p|] /=; last by rewrite IH1.
exact: neg_root_sound.
Qed.

Theorem radcan_eq_cond_rootf fa e1 e2 cs :
  radcan_check_rootf fa mo e1 e2 = Some cs ->
  all_conds cs -> rinterp r env e1 = rinterp r env e2.
Proof.
rewrite /radcan_check_rootf => /radcan_eq_cond_rawf H /H.
by rewrite !cb_rw_sound.
Qed.

Theorem radcan_eq_cond_root e1 e2 cs : radcan_check_root mo e1 e2 = Some cs ->
  all_conds cs -> rinterp r env e1 = rinterp r env e2.
Proof. exact: radcan_eq_cond_rootf. Qed.

End CondSound.

Section CondSound0.

Variable F : numFieldType.
Variable rt : nat -> F -> F.
Variable env : seq F.

Local Notation ri := (rinterp_gen rt env).
Local Notation atom_interp0 := (atom_interp0 rt env).
Local Notation vmono_interp0 := (vmono_interp0 rt env).
Local Notation holds0 := (holds0 rt env).
Local Notation nf_interp0 := (nf_interp0 rt env).
Local Notation cond_interp_gen := (cond_interp_gen rt env).
Local Notation all_conds_gen := (all_conds_gen rt env).

Local Arguments nf_add : simpl never.
Local Arguments nf_mul0 : simpl never.

Lemma vstrip_sound0 v a w : vstrip v a = Some w ->
  vmono_interp0 v = atom_interp0 a * vmono_interp0 w.
Proof.
elim: v w => [|[b k] v IH] w //=.
case: ifP => [/andP[/cmp_eqbP/atom_cmp_eq <- k0] [<-]|_].
  case: eqP => [k1|k1]; rewrite vmono_interp0_cons /=.
    by rewrite k1 expr1.
  by rewrite vmono_interp0_cons /= mulrA -exprS prednK.
case E : (vstrip v a) => [w'|] // [<-].
by rewrite !vmono_interp0_cons /= (IH _ E) mulrCA.
Qed.

Lemma split_inv_sound0 a p :
  nf_interp0 p = nf_interp0 (split_inv a p).1 * atom_interp0 a +
                 nf_interp0 (split_inv a p).2.
Proof.
elim: p => [|[c [v m]] p IH] /=; first by rewrite !nf_interp0_nil mul0r add0r.
case E : (vstrip v a) => [w|] /=;
  rewrite nf_interp0_cons IH !nf_add_sound0 !nf_interp0_cons !nf_interp0_nil
          !addr0 /=.
  rewrite (vstrip_sound0 E) mulrDl addrA; congr (_ + _ + _).
  move: (C2F c) (atom_interp0 a) (vmono_interp0 w) => x y z.
  by rewrite mulrCA mulrC.
by rewrite addrCA.
Qed.

Lemma cancel_one0_sound p e q c : cancel_one0 p e = Some (q, c) ->
  cond_interp_gen c -> nf_interp0 q = nf_interp0 p.
Proof.
rewrite /cancel_one0; have := split_inv_sound0 (AInv e) p.
case: split_inv => P R /= Hs.
case: P Hs => [|t P] Hs //.
set P0 := t :: P in Hs *.
case: pdiv => [Qt|].
  case: ifP => // /nf_eqb_eq0 HP [<- <-] /= Hc.
  by rewrite Hs HP nf_add_sound0 nf_mul0_sound -pnorm0_sound mulfK.
case: gcd_split => [[[G P'] D']|] //.
case: ifP => // /andP[/nf_eqb_eq0 HP /nf_eqb_eq0 HD] [<- <-] /=.
rewrite nf_to_rexpr0_sound => Hc.
rewrite Hs HP nf_add_sound0 !nf_mul0_sound (pnorm0_sound rt env e) HD.
rewrite nf_mul0_sound.
by rewrite nf_inv0_sound invfM mulrACA divff // mulr1.
Qed.

Lemma nf_cancel0_sound p : holds0 (nf_cancel0 p).2 ->
  nf_interp0 (nf_cancel0 p).1 = nf_interp0 p.
Proof.
rewrite /nf_cancel0.
have : forall l (acc : nf * seq cond),
    holds0 (foldl (fun acc e => if cancel_one0 acc.1 e is Some (q, c) then
                                 (q, rcons acc.2 c) else acc) acc l).2 ->
    holds0 acc.2 /\
    nf_interp0 (foldl (fun acc e => if cancel_one0 acc.1 e is Some (q, c) then
                                 (q, rcons acc.2 c) else acc) acc l).1 =
    nf_interp0 acc.1.
  elim=> [|e l IH] acc //=.
  case E : (cancel_one0 acc.1 e) => [[q c]|] /IH [] //=.
  rewrite -cats1 => /holds0_cat [H1 H2] ->; split=> //.
  by apply: cancel_one0_sound E _; apply: H2; left.
by move=> H /H [].
Qed.

Theorem normc0_sound e : holds0 (normc0 e).2 -> ri e = nf_interp0 (normc0 e).1.
Proof.
elim: e => [z|i|n p|n e1 IH1|e1 IH1 e2 IH2|e1 IH1|e1 IH1 e2 IH2|e1 IH1 e2 IH2|
            e1 IH1 k|e1 IH1] /=.
- by move=> _; rewrite nf_single_sound0 /= vmono_interp0_nil mulr1 C2F_c_of_Z.
- by move=> _; rewrite atom_nf_sound0.
- by move=> _; rewrite atom_nf_sound0.
- move: IH1; case: (normc0 e1) => p c1 /= IH1 /IH1 He.
  by rewrite atom_nf_sound0 /= nf_to_rexpr0_sound He.
- move: IH1 IH2; case: (normc0 e1) => p1 c1.
  case: (normc0 e2) => p2 c2 /= IH1 IH2.
  have := @nf_cancel0_sound (nf_add p1 p2); case: nf_cancel0 => s c3 /= Hs.
  case/holds0_cat => /IH1 -> /holds0_cat [/IH2 -> /Hs ->].
  by rewrite nf_add_sound0.
- move: IH1; case: (normc0 e1) => p c1 /= IH1 /IH1 ->.
  by rewrite nf_opp_sound0.
- move: IH1 IH2; case: (normc0 e1) => p1 c1.
  case: (normc0 e2) => p2 c2 /= IH1 IH2.
  have := @nf_cancel0_sound (nf_add p1 (nf_opp p2)).
  case: nf_cancel0 => s c3 /= Hs.
  case/holds0_cat => /IH1 -> /holds0_cat [/IH2 -> /Hs ->].
  by rewrite nf_add_sound0 nf_opp_sound0.
- move: IH1 IH2; case: (normc0 e1) => p1 c1.
  case: (normc0 e2) => p2 c2 /= IH1 IH2.
  have := @nf_cancel0_sound (nf_mul0 p1 p2); case: nf_cancel0 => s c3 /= Hs.
  case/holds0_cat => /IH1 -> /holds0_cat [/IH2 -> /Hs ->].
  by rewrite nf_mul0_sound.
- move: IH1; case: (normc0 e1) => p c1 /= IH1.
  have := @nf_cancel0_sound (nf_pow0 p k); case: nf_cancel0 => s c3 /= Hs.
  case/holds0_cat => /IH1 -> /Hs ->.
  by rewrite nf_pow0_sound.
move: IH1; case: (normc0 e1) => p c1 /= IH1.
have := @nf_cancel0_sound (nf_inv0 p); case: nf_cancel0 => s c3 /= Hs.
case/holds0_cat => /IH1 -> /Hs ->.
by rewrite nf_inv0_sound.
Qed.

Theorem radcan_check0_sound e1 e2 cs : radcan_check0 e1 e2 = Some cs ->
  all_conds_gen cs -> ri e1 = ri e2.
Proof.
rewrite /radcan_check0.
have := @normc0_sound e1; case: (normc0 e1) => p1 c1 /= H1.
have := @normc0_sound e2; case: (normc0 e2) => p2 c2 /= H2.
case: ifP => // /nf_eqb_eq0 Hp [<-].
move=> /all_conds_genP /holds0_dedup /holds0_cat [/H1 -> /H2 ->].
by rewrite Hp.
Qed.

End CondSound0.

(* The decision theorems used by the tactics *)

Theorem radcan_eq_cond (F : numFieldType) (r : posroot F) (env : seq F)
    e1 e2 cs :
  radcan_check e1 e2 = Some cs -> all_conds r env cs ->
  rinterp r env e1 = rinterp r env e2.
Proof.
rewrite /radcan_check; case: ifP => _ H Hc.
  exact: (radcan_check0_sound H (all_conds_bridge Hc)).
case/ocase_some: H => H; first exact: radcan_eq_cond_root H Hc.
exact: radcan_eq_cond_rootf H Hc.
Qed.

Theorem radcan_eq_cond_odd (F : numFieldType) (r : posroot F) (o : oddroot r)
    (env : seq F) e1 e2 cs :
  radcan_check_odd e1 e2 = Some cs -> all_conds r env cs ->
  rinterp r env e1 = rinterp r env e2.
Proof.
rewrite /radcan_check_odd; case: ifP => _ H Hc.
  exact: (radcan_check0_sound H (all_conds_bridge Hc)).
case/ocase_some: H => H; first exact: radcan_eq_cond_root H Hc.
exact: radcan_eq_cond_rootf H Hc.
Qed.

Theorem radcan_eq_odd (F : numFieldType) (r : posroot F) (o : oddroot r)
    (env : seq F) e1 e2 :
  radcan_check_odd e1 e2 = Some [::] -> rinterp r env e1 = rinterp r env e2.
Proof. by move/(radcan_eq_cond_odd o); apply. Qed.

Theorem radcan_eq_cond_neg (F : numFieldType) (r : posroot F) (w : negroot r)
    (env : seq F) e1 e2 cs :
  radcan_check_neg e1 e2 = Some cs -> all_conds r env cs ->
  rinterp r env e1 = rinterp r env e2.
Proof.
rewrite /radcan_check_neg; case: ifP => _ H Hc.
  exact: (radcan_check0_sound H (all_conds_bridge Hc)).
case/ocase_some: H => H; first exact: radcan_eq_cond_root H Hc.
case/ocase_some: H => H; first exact: radcan_eq_cond_root H Hc.
by case/ocase_some: H => H; exact: radcan_eq_cond_rootf H Hc.
Qed.

Theorem radcan_eq_neg (F : numFieldType) (r : posroot F) (w : negroot r)
    (env : seq F) e1 e2 :
  radcan_check_neg e1 e2 = Some [::] -> rinterp r env e1 = rinterp r env e2.
Proof. by move/(radcan_eq_cond_neg w); apply. Qed.

Theorem radcan_eq_cond_real (F : numFieldType) (r : posroot F)
    (rl : realroot r) (env : seq F) e1 e2 cs :
  radcan_check_real e1 e2 = Some cs -> all_conds r env cs ->
  rinterp r env e1 = rinterp r env e2.
Proof.
have o := realroot_odd rl.
rewrite /radcan_check_real; case: ifP => _ H Hc.
  exact: (radcan_check0_sound H (all_conds_bridge Hc)).
case/ocase_some: H => H; first exact: radcan_eq_cond_root H Hc.
case/ocase_some: H => H; first exact: radcan_eq_cond_root H Hc.
by case/ocase_some: H => H; exact: radcan_eq_cond_rootf H Hc.
Qed.

Theorem radcan_eq_real (F : numFieldType) (r : posroot F) (rl : realroot r)
    (env : seq F) e1 e2 :
  radcan_check_real e1 e2 = Some [::] -> rinterp r env e1 = rinterp r env e2.
Proof. by move/(radcan_eq_cond_real rl); apply. Qed.

Theorem radcan_eq (F : numFieldType) (r : posroot F) (env : seq F) e1 e2 :
  radcan_check e1 e2 = Some [::] -> rinterp r env e1 = rinterp r env e2.
Proof. by move/radcan_eq_cond; apply. Qed.

(* root-free goals, no posroot needed *)
Theorem radcan_eq_cond0 (F : numFieldType) (env : seq F) e1 e2 cs :
  no_root e1 -> no_root e2 -> radcan_check e1 e2 = Some cs ->
  all_conds0 env cs -> rinterp0 env e1 = rinterp0 env e2.
Proof.
by move=> n1 n2; rewrite /radcan_check n1 n2 /=; exact: radcan_check0_sound.
Qed.

End RadcanF.
