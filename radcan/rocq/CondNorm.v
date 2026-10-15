(******************************************************************************)
(* CondNorm: the normaliser with side conditions, and its soundness.          *)
(*   normc m hs bs e  == normal form of e and its side conditions             *)
(*   normcr true      == the same, with denominators mixing variables and     *)
(*                      roots rationalised (M11, Ratio.v); radcan_check_raw   *)
(*                      uses it only when the plain normal forms differ       *)
(*   mk_basis_n       == basis of the radicands, plus the square-free factors *)
(*                      of nested radicands whose normal form is root-free    *)
(*   radcan_check_irr == the basis refined by irreducible factors (M16, form  *)
(*                      1, Poly.irr_basis): stronger conditions, tried last   *)
(*   cb_rw m cb e     == constant radicands over a common coprime basis       *)
(*   radcan_check_rootf fa m == the checker of mode m (cb_rw, then normc)     *)
(*   normc0 e         == root-free normaliser (sound for any root function)   *)
(*   radcan_eq_cond_rootf, radcan_check0_sound == their soundness             *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt ZArith Lia.
From Stdlib Require Import QArith_base Qreduction.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts Syntax Backend Mono Factor NF.
From Radcan Require Import Inverse Poly Ratio RealRoot.
From Radcan Require Import OmegaRoot2 CondSimp CondRoot.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module CondNormF (Import N : NUM).

Include CondRootF N.

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

(* Omega6 (mode MNegS): when the normal forms differ, the square roots
   sqrt 2 = w4 - w4 ^+ 3, sqrt 3 = w6 - w6 ^+ 5, sqrt 5 = 2 w5 - 2 w5 ^+ 4 - 1
   (wn = omega_n) are substituted, sqrt D only when the lcm N of the omega
   indices of both normal forms is a multiple of 4, 6, 5 resp.; only the
   constant square roots of the root monomials (fct (b, 2, e), D | b) *)
Definition om_lcm (p : nf) : nat :=
  foldr (fun t acc =>
           foldr (fun ak acc =>
                    if ak.1 is ARoot n e then
                      if is_omega e then lcmn (Pos.to_nat n) acc else acc
                    else acc) acc t.2.1) 1%N p.

Definition om_pow (n : positive) (k : nat) : nf := nf_pow (omega_nf n) k.

Definition sq_G2 : nf := nf_add (om_pow 4 1) (nf_opp (om_pow 4 3)).
Definition sq_G3 : nf := nf_add (om_pow 6 1) (nf_opp (om_pow 6 5)).
Definition sq_G5 : nf :=
  nf_add (nf_add (om_pow 5 1) (om_pow 5 1))
         (nf_opp (nf_add (nf_add (om_pow 5 4) (om_pow 5 4)) nf_one)).

(* b = q * D *)
Definition sq_div (D b : positive) : option positive :=
  if Z.div (Zpos b) (Zpos D) is Zpos q then
    if Pos.eqb (Pos.mul q D) b then Some q else None
  else None.

(* m = (q * D, 2, e) :: w up to order *)
Fixpoint mfind (D : positive) (m : mono) : option (positive * nat * mono) :=
  match m with
  | [::] => None
  | (b, n, e) :: m' =>
    let rest := if mfind D m' is Some (q, e', w) then
                  Some (q, e', (b, n, e) :: w) else None in
    if n == 2%N then
      (if sq_div D b is Some q then Some (q, e, m') else rest)
    else rest
  end.

Definition sq_term (D : positive) (G : nf) (t : coef * key) : nf :=
  if mfind D t.2.2 is Some (q, e, w) then
    nf_mul [:: (t.1, (t.2.1, w))]
      (nf_mul (if Pos.eqb q 1 then nf_one
               else [:: (c_one, ([::], [:: (q, 2%N, e)]))])
              (nf_pow G e))
  else [:: t].

Definition sq_step (N k : nat) (D : positive) (G : nf) (p : nf) : nf :=
  if (k %| N)%N then foldr (fun t acc => nf_add (sq_term D G t) acc) [::] p
  else p.

Definition sq_subst (N : nat) (p : nf) : nf :=
  sq_step N 5 5 sq_G5 (sq_step N 6 3 sq_G3 (sq_step N 4 2 sq_G2 p)).

Definition sq_check (m : rmode) (p1 p2 : nf) (cs : seq cond) :
  option (seq cond) :=
  let N := lcmn (om_lcm p1) (om_lcm p2) in
  let: (s1, c1) := nf_simp m (sq_subst N p1) in
  let: (s2, c2) := nf_simp m (sq_subst N p2) in
  if nf_eqb s1 s2 then Some (cs ++ c1 ++ c2) else None.

Definition radcan_check_bs (rt : bool) (m : rmode) (hs bs : seq nf)
  (e1 e2 : rexpr) : option (seq cond) :=
  let: (p1, p2, cs) := radcan_nfb rt m hs bs e1 e2 in
  if nf_eqb p1 p2 then Some cs else
  if sq_mode m then sq_check m p1 p2 cs else None.

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

Lemma ocase_some (T : Type) (a b : option T) x :
  (if a is Some y then Some y else b) = Some x -> a = Some x \/ b = Some x.
Proof. by case: a => [y [->]|]; [left | right]. Qed.
Arguments ocase_some {T a b x}.

Local Open Scope ring_scope.

Section CondNormSound.

Variable F : numFieldType.
Variable r : posroot F.
Variable env : seq F.
(* odd mode: only used with an oddroot, neg mode: only with a negroot *)
Variable mo : rmode.
Hypothesis Ho : odd_mode mo -> oddroot r.
Hypothesis Hng : neg_mode mo -> negroot r.
Hypothesis Hrl : real_mode mo -> realroot r.
Hypothesis Hcy : cyc_mode mo -> windex r.
Hypothesis Hsq : sq_mode mo -> wsqrt r.

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

Local Notation nf_simp_sound := (@nf_simp_sound F r env mo Hng Hrl Hcy).
Local Notation nf_rootE_sound := (@nf_rootE_sound F r env mo Ho Hng Hrl).
Local Notation nf_inv_m_sound := (@nf_inv_m_sound F r env mo Hng).

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

(* Omega6: the substitution of the square roots *)

Lemma sq_div_sound D b q : sq_div D b = Some q ->
  pos2F F b = pos2F F q * pos2F F D.
Proof.
rewrite /sq_div; case: Z.div => // q'.
by case: ifP => // /Pos.eqb_eq <- [<-]; exact: pos2F_mul.
Qed.

Lemma mfind_sound D m q e w : mfind D m = Some (q, e, w) ->
  mono_interp m =
  (proot r 2 (pos2F F q) * proot r 2 (pos2F F D)) ^+ e * mono_interp w.
Proof.
elim: m q e w => [|[[b n] e'] m IH] q e w //=.
have Hrest : (if mfind D m is Some (q', e'', w') then
                Some (q', e'', (b, n, e') :: w') else None) =
             Some (q, e, w) ->
             mono_interp ((b, n, e') :: m) =
  (proot r 2 (pos2F F q) * proot r 2 (pos2F F D)) ^+ e * mono_interp w.
  case E : (mfind D m) => [[[q1 e1] w1]|] // [<- <- <-].
  by rewrite !mono_interp_cons (IH _ _ _ E) mulrCA.
case: eqP => [n2|_ /Hrest //].
case E : (sq_div D b) => [q'|]; last exact: Hrest.
move=> [<- <- <-]; rewrite mono_interp_cons /= n2 (sq_div_sound E).
by rewrite prootM ?pos2F_ge0.
Qed.

Lemma sq_term_sound D G t : nf_interp G = proot r 2 (pos2F F D) ->
  nf_interp (sq_term D G t) = C2F t.1 * key_interp t.2.
Proof.
move=> HG; case: t => c [v m]; rewrite /sq_term /=.
case E : (mfind D m) => [[[q e] w]|]; last first.
  by rewrite nf_interp_cons nf_interp_nil addr0.
rewrite !nf_mul_sound nf_pow_sound HG nf_interp_cons nf_interp_nil addr0.
have -> : nf_interp (if Pos.eqb q 1 then nf_one
                     else [:: (c_one, ([::], [:: (q, 2%N, e)]))]) =
          proot r 2 (pos2F F q) ^+ e.
  case: ifP => [/Pos.eqb_eq ->|_].
    by rewrite nf_one_sound pos2F1 proot_1 // expr1n.
  rewrite nf_interp_cons nf_interp_nil addr0 C2F_c_one mul1r /key_interp /=.
  by rewrite vmono_interp_nil mul1r mono_interp_cons mono_interp_nil mulr1.
rewrite /key_interp /= (mfind_sound E) exprMn.
move: (C2F c) (vmono_interp v) (mono_interp w) (proot _ _ _ ^+ e)
  (proot _ _ (pos2F F D) ^+ e) => a b x y z.
by rewrite -!mulrA [x * _]mulrC -mulrA.
Qed.

Lemma sq_step_sound N k D G p : nf_interp G = proot r 2 (pos2F F D) ->
  nf_interp (sq_step N k D G p) = nf_interp p.
Proof.
move=> HG; rewrite /sq_step; case: ifP => // _.
elim: p => [|t p IH] //=.
by rewrite nf_add_sound IH sq_term_sound // nf_interp_cons.
Qed.

Lemma om_pow_sound n k :
  nf_interp (om_pow n k) = proot r (Pos.to_nat n) (-1) ^+ k.
Proof.
rewrite /om_pow nf_pow_sound /omega_nf /root_atom nf_interp_cons nf_interp_nil.
rewrite addr0 C2F_c_one mul1r /key_interp mono_interp_nil mulr1 /=.
by rewrite vmono_interp_cons vmono_interp_nil mulr1 expr1 /= pos2F1.
Qed.

Lemma sq_subst_sound N p : wsqrt r -> nf_interp (sq_subst N p) = nf_interp p.
Proof.
case=> h2 h3 h5; rewrite /sq_subst !sq_step_sound //.
- rewrite /sq_G2; move: (om_pow_sound 4 1) (om_pow_sound 4 3).
  move: (om_pow 4 1) (om_pow 4 3) => a b Ha Hb.
  by rewrite nf_add_sound nf_opp_sound Ha Hb expr1 h2.
- rewrite /sq_G3; move: (om_pow_sound 6 1) (om_pow_sound 6 5).
  move: (om_pow 6 1) (om_pow 6 5) => a b Ha Hb.
  by rewrite nf_add_sound nf_opp_sound Ha Hb expr1 h3.
have Hc : nf_interp nf_one = 1 := nf_one_sound _ _.
rewrite /sq_G5; move: (om_pow_sound 5 1) (om_pow_sound 5 4) Hc.
move: (om_pow 5 1) (om_pow 5 4) nf_one => a b c Ha Hb Hc.
rewrite !nf_add_sound nf_opp_sound !nf_add_sound Ha Hb Hc expr1 h5.
by rewrite mulr_natl (mulr_natl (_ ^+ 4)) !mulr2n opprD addrA.
Qed.

(* any basis: it only guides decompose, whose results are checked *)
Lemma radcan_check_bs_sound rt hs bs e1 e2 cs :
  radcan_check_bs rt mo hs bs e1 e2 = Some cs ->
  all_conds cs -> rinterp r env e1 = rinterp r env e2.
Proof.
rewrite /radcan_check_bs /radcan_nfb.
have := @normcr_sound rt hs bs e1; case: (normcr _ _ _ _ e1) => p1 c1 /= H1.
have := @normcr_sound rt hs bs e2; case: (normcr _ _ _ _ e2) => p2 c2 /= H2.
case: ifP => [/nf_eqb_eq Hp [<-]|_].
  move=> /all_condsP /cfilter_sound /holds_dedup /holds_cat [/H1 -> /H2 ->].
  by rewrite Hp.
case: ifP => // Hm; rewrite /sq_check.
set N := lcmn _ _; have hs2 := Hsq Hm.
have := @nf_simp_sound (sq_subst N p1); case: nf_simp => s1 d1 /= E1.
have := @nf_simp_sound (sq_subst N p2); case: nf_simp => s2 d2 /= E2.
case: ifP => // /nf_eqb_eq Hs [<-] /all_condsP /holds_cat [].
move=> /cfilter_sound /holds_dedup /holds_cat [/H1 -> /H2 ->].
move=> /holds_cat [/E1 F1 /E2 F2].
by rewrite -(sq_subst_sound N p1 hs2) -F1 Hs F2 sq_subst_sound.
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

End CondNormSound.

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

End CondNormF.
