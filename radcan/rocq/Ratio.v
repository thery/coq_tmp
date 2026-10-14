(* Ratio (M11): rationalising denominators that mix variables and roots.     *)
(*   rat_gens d    == the root atoms ARoot n e of d, with their index n       *)
(*   rat_basis d   == the basis of root monomials of d: products of the root *)
(*                    atoms (exponents < n) and of the integer root monomials *)
(*                    (Inverse.v, nf_basis), as keys (vmono, mono)            *)
(*   rat_red p     == p with proot n e ^+ k (k >= n) reduced (unchecked)     *)
(*   rat_matrix d  == the matrix of the multiplication by d on the basis,     *)
(*                    entries are polynomials (no root of the basis)          *)
(*   ffgj          == fraction-free Gauss-Jordan elimination (Bareiss), with *)
(*                    exact polynomial divisions (Poly.v)                     *)
(*   nf_rat_inv d  == Some (u, E), E root-free, primitive, positive leading   *)
(*                    coefficient, u and E without common polynomial factor,  *)
(*                    d * u = E intended (unverified computation)             *)
(*   rat_check simp d u E == Some cs when simp (d * u) is E, simp being a     *)
(*                    simplification with side conditions (nf_simp, Cond.v)   *)
(*   nf_inv_rat simp d == Some (u * E^-1, conditions): the inverse of d,      *)
(*                    conditions E != 0 and those of the check                *)
(* Soundness: inv_from_mul (d * u = E -> E != 0 -> d^-1 = u * E^-1),         *)
(*   rat_check_sound, nf_inv_rat_sound.                                       *)

From Stdlib Require Import BinNums BinPos BinInt ZArith Lia.
From Stdlib Require Import QArith_base Qreduction.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts Syntax Backend Mono Factor NF.
From Radcan Require Import Inverse Poly.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(* the field lemma behind the rationalisation *)
Lemma inv_from_mul (F : fieldType) (d u E : F) :
  d * u = E -> E != 0 -> d^-1 = u * E^-1.
Proof.
move=> dE E0; have u0 : u != 0.
  by apply: contraNneq E0 => u0; rewrite -dE u0 mulr0.
by rewrite -dE invfM mulrCA divff // mulr1.
Qed.

Local Close Scope ring_scope.

Module RatioF (Import N : NUM).

Include PolyF N.

(* ------------------------------------------------------------------------ *)
(* The basis of root monomials                                              *)
(* ------------------------------------------------------------------------ *)

(* the root atoms of d with their index *)
Definition rat_gens (d : nf) : seq (atom * nat) :=
  foldr (fun t acc =>
           foldr (fun ak acc =>
                    if ak.1 is ARoot n _ then
                      if has (fun bk => atom_eqb bk.1 ak.1) acc then acc
                      else (ak.1, Pos.to_nat n) :: acc
                    else acc) acc t.2.1) [::] d.

Definition rat_is_gen (gs : seq (atom * nat)) (a : atom) : bool :=
  has (fun bk => atom_eqb bk.1 a) gs.

(* the products of the root atoms, exponents below their index *)
Definition rat_vbasis (gs : seq (atom * nat)) : seq vmono :=
  foldr (fun an acc =>
           flatten (map (fun e =>
                           map (fun v => vmono_mul (vsingle an.1 e) v) acc)
                        (iota 0 an.2)))
        [:: [::]] gs.

Definition rat_dim (d : nf) : nat :=
  (foldr (fun bn a => bn.2 * a) 1 (nf_bases d) *
   foldr (fun an a => an.2 * a) 1 (rat_gens d))%N.

Definition rat_basis (d : nf) : seq key :=
  let ms := nf_basis (nf_bases d) in
  flatten (map (fun v => map (fun m => (v, m)) ms) (rat_vbasis (rat_gens d))).

(* a variable monomial split into its root part and its polynomial part *)
Definition rat_vsplit (gs : seq (atom * nat)) (v : vmono) : vmono * vmono :=
  (filter (fun ak => rat_is_gen gs ak.1) v,
   filter (fun ak => ~~ rat_is_gen gs ak.1) v).

(* the polynomial coefficient of the basis element b in p *)
Definition rat_coef (gs : seq (atom * nat)) (b : key) (p : nf) : nf :=
  foldr (fun t acc =>
           let: (va, vr) := rat_vsplit gs t.2.1 in
           if cmp_eqb (vmono_cmp va b.1) && cmp_eqb (mono_cmp t.2.2 b.2) then
             nf_add [:: (t.1, (vr, [::]))] acc
           else acc) [::] p.

(* ------------------------------------------------------------------------ *)
(* Reduction of proot n e ^+ k, k >= n (unchecked, the result of the        *)
(* rationalisation is checked by the caller)                                 *)
(* ------------------------------------------------------------------------ *)

Fixpoint rat_vextract (v : vmono) : option (positive * rexpr * nat * vmono) :=
  match v with
  | [::] => None
  | (a, k) :: v' =>
    let rest := if rat_vextract v' is Some (n', e', k', w) then
                  Some (n', e', k', (a, k) :: w) else None in
    if a is ARoot n e then
      (if (Pos.to_nat n <= k)%N then Some (n, e, k, v') else rest)
    else rest
  end.

Definition rat_red_term (t : coef * key) : nf :=
  if rat_vextract t.2.1 is Some (n, e, k, w) then
    let N := Pos.to_nat n in
    nf_mul [:: (t.1, (vmono_mul (vsingle (ARoot n e) (k %% N)) w, t.2.2))]
           (nf_pow (pnorm e) (k %/ N))
  else [:: t].

Fixpoint rat_red (fuel : nat) (p : nf) : nf :=
  match fuel with
  | O => p
  | S f =>
    if has (fun t => if rat_vextract t.2.1 is Some _ then true else false) p
    then
      rat_red f (foldr (fun t acc => nf_add (rat_red_term t) acc) [::] p)
    else p
  end.

(* ------------------------------------------------------------------------ *)
(* The matrix of the multiplication by d: the column of b_j holds the       *)
(* coefficients of d * b_j; the last column is the right-hand side e_1      *)
(* ------------------------------------------------------------------------ *)

Definition rat_matrix (d : nf) : option (seq key * seq (seq nf)) :=
  if (rat_dim d > max_dim)%N then None else
  let gs := rat_gens d in
  let B := rat_basis d in
  let cols := map (fun b => rat_red 16 (nf_mul d [:: (c_one, b)])) B in
  Some (B, map (fun bi => rcons (map (rat_coef gs bi) cols)
                                (rat_coef gs bi nf_one)) B).

(* ------------------------------------------------------------------------ *)
(* Fraction-free Gauss-Jordan elimination (Bareiss, one step):              *)
(*   a_ij <- (a_kk * a_ij - a_ik * a_kj) / p, p the previous pivot,         *)
(* for every row i but the pivot row k.  The divisions are exact (every      *)
(* entry is a minor), at the end the diagonal is det and the last column    *)
(* det * M^-1 e_1.                                                           *)
(* ------------------------------------------------------------------------ *)

Definition rat_fuel := (256 * 256)%N.

Definition rat_pdiv (p b : nf) : nf :=
  if nf_eqb b nf_one then p
  else if pdiv_loop rat_fuel p b [::] is Some q then q else p.

(* the nonzero entry of column c with the fewest terms *)
Fixpoint rat_pick (c i : nat) (todo : seq (seq nf)) (best : option (nat * nat))
  : option (nat * nat) :=
  match todo with
  | [::] => best
  | rw :: todo' =>
    let s := size (nth [::] rw c) in
    let best' := if s is O then best else
                 if best is Some (_, sb) then
                   (if (s < sb)%N then Some (i, s) else best)
                 else Some (i, s) in
    rat_pick c i.+1 todo' best'
  end.

Fixpoint ffgj (c fuel : nat) (prev : nf) (done todo : seq (seq nf))
  : option (nf * seq (seq nf)) :=
  match fuel with
  | O => Some (prev, done)
  | S f =>
    if rat_pick c 0 todo None is Some (k, _) then
      let p := nth [::] todo k in
      let rest := take k todo ++ drop k.+1 todo in
      let pv := nth [::] p c in
      let upd := fun rw =>
        let a := nth [::] rw c in
        map (fun xy => rat_pdiv (psub (nf_mul pv xy.1) (nf_mul a xy.2)) prev)
            (zip rw p) in
      ffgj c.+1 f pv (rcons (map upd done) p) (map upd rest)
    else None
  end.

(* ------------------------------------------------------------------------ *)
(* d * u = E, E root-free                                                    *)
(* ------------------------------------------------------------------------ *)

Definition rat_rootfree (gs : seq (atom * nat)) (p : nf) : bool :=
  all (fun t => nilp t.2.2 && ~~ has (fun ak => rat_is_gen gs ak.1) t.2.1) p.

Definition nf_rat_inv (d : nf) : option (nf * nf) :=
  if rat_matrix d is Some (B, rows) then
    if ffgj 0 (size B) nf_one [::] rows is Some (E0, done) then
      let us0 := map (last [::]) done in
      (* the common factor of E and of the coefficients of u *)
      let g := foldl (fun g q => if isconst g then g else pgcd gcd_fuel g q)
                     E0 us0 in
      let: (E1, us1) := if isconst g then (E0, us0)
                        else (pexdiv E0 g, map (fun q => pexdiv q g) us0) in
      (* E primitive with a positive leading coefficient *)
      let: (c, E2) := nf_prim E1 in
      let: (E, us) := if prim_ok E1 c E2 then (E2, map (nf_scale (c_inv c)) us1)
                      else (E1, us1) in
      let u := foldr (fun bq acc => nf_add (nf_mul bq.2 [:: (c_one, bq.1)]) acc)
                     [::] (zip B us) in
      if ~~ nilp E && rat_rootfree (rat_gens d) E &&
         nf_eqb (rat_red 16 (nf_mul d u)) E then Some (u, E)
      else None
    else None
  else None.

(* ------------------------------------------------------------------------ *)
(* The check and the inverse, for a simplification simp with side           *)
(* conditions (nf_simp mo in Cond.v)                                         *)
(* ------------------------------------------------------------------------ *)

Definition rat_check (simp : nf -> nf * seq cond) (d u E : nf) :
  option (seq cond) :=
  let: (s, cs) := simp (nf_mul d u) in
  if nf_eqb s E then Some cs else None.

Definition nf_inv_rat (simp : nf -> nf * seq cond) (d : nf) :
  option (nf * seq cond) :=
  if nf_rat_inv d is Some (u, E) then
    if nf_wf E then
      if rat_check simp d u E is Some cs then
        let: (Ei, cs') := nf_inv (nf_to_rexpr E) E in
        Some (nf_mul u Ei, CNeq0 (nf_to_rexpr E) :: cs ++ cs')
      else None
    else None
  else None.

Local Open Scope ring_scope.

Section RatioSound.

Variable F : numFieldType.
Variable r : posroot F.
Variable env : seq F.

Local Notation holds := (holds r env).
Local Notation nf_interp := (nf_interp r env).
Local Notation cond_interp := (cond_interp r env).

Variable simp : nf -> nf * seq cond.
Hypothesis simp_sound :
  forall p, holds (simp p).2 -> nf_interp (simp p).1 = nf_interp p.

Lemma rat_check_sound d u E cs : rat_check simp d u E = Some cs -> holds cs ->
  nf_interp d * nf_interp u = nf_interp E.
Proof.
rewrite /rat_check; have := @simp_sound (nf_mul d u).
case: (simp _) => s cs' /= Hs.
case: ifP => // /nf_eqb_eq HE [<-] /Hs.
by rewrite nf_mul_sound -HE.
Qed.

Lemma nf_inv_rat_sound d q cs : nf_inv_rat simp d = Some (q, cs) -> holds cs ->
  nf_interp q = (nf_interp d)^-1.
Proof.
rewrite /nf_inv_rat; case: nf_rat_inv => [[u E]|] //.
case: ifP => // wE; case Ec : (rat_check simp d u E) => [cs1|] //.
have := @nf_inv_sound F r env (nf_to_rexpr E) E (nf_to_rexpr_sound r env wE).
case: nf_inv => Ei cs2 HEi [<- <-] /holds_cons [/= HE0 /holds_cat [H1 H2]].
rewrite nf_to_rexpr_sound // in HE0.
rewrite nf_mul_sound (HEi H2) (inv_from_mul (rat_check_sound Ec H1) HE0).
by [].
Qed.

End RatioSound.

End RatioF.
