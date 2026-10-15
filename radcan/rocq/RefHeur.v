(******************************************************************************)
(* RefHeur: the unverified search of the refinement (no proofs here).         *)
(*   fm_cert fs s P == certificate (ls, c0) for comb_check found by           *)
(*                     Fourier-Motzkin elimination (monomials read as         *)
(*                     independent unknowns)                                  *)
(*   fimp rs f  == the fact f follows from rs (ptriv, rimp1 or comb_check)    *)
(*   implied rs c == the raw condition c follows from rs                      *)
(*   refine_raw cs == the guessed refined conditions: a condition is read as  *)
(* a fact 0 <= P or P != 0 (a product P gives one fact per factor); facts     *)
(* true on constants are dropped, the others divided by their content;        *)
(* affine facts in one variable become the strongest bounds (an interval      *)
(* when both exist and differ, even a contradictory one); the others are      *)
(* grouped by non-constant part, P != 0 is merged into 0 <= P (0 < P) or      *)
(* dropped, and printed with negative terms and constant on the other side;   *)
(* a general condition implied by the remaining ones is dropped.              *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt ZArith Lia.
From Stdlib Require Import QArith_base Qreduction.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot Syntax Radcan RefPoly RefCheck.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Q_scope.

(* Fourier-Motzkin search of a certificate (unverified) *)

(* a row: linear form, strict, multipliers of the facts, multiplier of -P *)
Definition row := (poly * bool * seq Q * Q)%type.

Fixpoint pcoef (m : amono) (p : poly) : Q :=
  if p is (c, m') :: p' then
    (if cmp_eqb (amono_cmp m m') then c else pcoef m p')
  else 0.

Definition rlin (a : Q) (r1 : row) (b : Q) (r2 : row) : row :=
  let: (p1, s1, l1, u1) := r1 in let: (p2, s2, l2, u2) := r2 in
  (padd (pscale a p1) (pscale b p2), s1 || s2,
   map (fun xy => Qred (a * xy.1 + b * xy.2)) (zip l1 l2),
   Qred (a * u1 + b * u2)).

Definition fm_cap := 400%N.

(* eliminate the monomial m *)
Definition fm_elim (rows : seq row) (m : amono) : seq row :=
  let co (r : row) := pcoef m r.1.1.1 in
  let pos := filter (fun r => qlt 0 (co r)) rows in
  let neg := filter (fun r => qlt (co r) 0) rows in
  let zer := filter (fun r => qz (co r)) rows in
  take fm_cap
    (zer ++ flatten (map (fun p => map (fun n => rlin (- co n) p (co p) n)
                                       neg) pos)).

Definition fm_mons (rows : seq row) : seq amono :=
  foldr (fun r acc =>
    foldr (fun t acc =>
      if t.2 is [::] then acc
      else if has (fun m => cmp_eqb (amono_cmp t.2 m)) acc then acc
      else t.2 :: acc) acc r.1.1.1) [::] rows.

(* rows of fs and of 0 <= -P, all monomials eliminated *)
Definition fm_rows (fs : seq fact) (P : poly) : seq row :=
  let n := size fs in
  let unit j := mkseq (fun k => if k == j then 1 else 0) n in
  let rows :=
    (pscale (-1) P, false, nseq n 0, 1) ::
    pmap (fun fj => let: (f, j) := fj in
           let s := if f.1 is KGt then true else false in
           if is_ge f then Some (f.2, s, unit j, 0) else None)
         (zip fs (iota 0 n)) in
  foldl fm_elim rows (fm_mons rows).

Definition fm_cert (fs : seq fact) (strict : bool) (P : poly) :
  option (seq Q * Q) :=
  let ok (r : row) :=
    let: (p, s, _, u) := r in
    let c := pconst_of p in
    qlt 0 u && Qle_bool c 0 && (~~ strict || qlt c 0 || s) in
  if filter ok (fm_rows fs P) is (p, _, ls, u) :: _ then
    Some (map (fun l => Qred (l / u)) ls, Qred (- pconst_of p / u))
  else None.

Definition comb1 (fs : seq fact) (strict : bool) (P : poly) : bool :=
  if fm_cert fs strict P is Some (ls, c0) then comb_check fs strict P ls c0
  else false.

(* the fact f is a combination of the facts fs *)
Definition fcomb (fs : seq fact) (f : fact) : bool :=
  let: (k, P) := f in
  match k with
  | KGe => comb1 fs false P
  | KGt => comb1 fs true P
  | KNe => comb1 fs true P || comb1 fs true (pscale (-1) P)
  end.

Definition fimp (rs : seq rcond) (f : fact) : bool :=
  let fs := flatten (map rfacts rs) in
  [|| ptriv f, has (fun r => rimp1 r f) fs | fcomb fs f].

Definition implied (rs : seq rcond) (c : cond) : bool :=
  match c with
  | CGe0 e => fimp rs (KGe, pnorm e)
  | CNeq0 e => fimp rs (KNe, pnorm e) || all (fun p => fimp rs (KNe, p)) (nzf e)
  end.

(* The heuristics (unverified) *)

Definition facts_of (c : cond) : seq fact :=
  match c with
  | CGe0 e => [:: (KGe, pnorm e)]
  | CNeq0 e => map (fun p => (KNe, p)) (nzf e)
  end.

(* the positive k such that k * p has coprime integer coefficients *)
Definition pcontent (p : poly) : Q :=
  let n := foldr (fun t g => Z.gcd (Qnum t.1) g) Z0 p in
  let d := foldr (fun t l => Z.lcm (Zpos (Qden t.1)) l) (Zpos xH) p in
  if Z.eqb n Z0 then 1 else Qmake d (Z.to_pos n).

Definition plead_neg (p : poly) : bool :=
  if pnc p is (c, _) :: _ then qlt c 0 else false.

Definition normf (f : fact) : fact :=
  let: (k, P) := f in
  let s := pcontent P in
  (k, pscale (if (if k is KNe then plead_neg P else false) then - s else s) P).

(* affine facts in one variable, as bounds *)
Definition old_of (f : fact) : option (rc Q) :=
  let: (k, P) := f in
  match pnc P with
  | [:: (a, [:: (RVar i, 1%N)])] =>
    let v := Qred (- pconst_of P / a) in
    match k with
    | KNe => Some (RNeq i v)
    | _ => Some (if Qle_bool 0 a then RLow false v i else RUpp false v i)
    end
  | _ => None
  end.

Definition rc_atom (f : rc Q) : option nat :=
  match f with
  | RLow _ _ i | RUpp _ _ i | RInt _ _ i _ _ | RNeq i _ => Some i
  | _ => None
  end.

Definition low_of (i : nat) (f : rc Q) : option (bool * Q) :=
  if f is RLow s v j then (if Nat.eqb i j then Some (s, v) else None) else None.

Definition upp_of (i : nat) (f : rc Q) : option (bool * Q) :=
  if f is RUpp s v j then (if Nat.eqb i j then Some (s, v) else None) else None.

Definition neq_of (i : nat) (f : rc Q) : option Q :=
  if f is RNeq j v then (if Nat.eqb i j then Some v else None) else None.

(* the stronger of two lower (up = false) or upper (up = true) bounds *)
Definition best (up : bool) (o : option (bool * Q)) (sv : bool * Q) :
  option (bool * Q) :=
  match o with
  | None => Some sv
  | Some (s1, v1) =>
    let: (s2, v2) := sv in
    if Qeq_bool v1 v2 then Some (s1 || s2, v1)
    else if Qle_bool v1 v2 (+) up then Some (s2, v2) else Some (s1, v1)
  end.

Fixpoint qundup (l : seq Q) : seq Q :=
  match l with
  | [::] => [::]
  | v :: l' => if has (Qeq_bool v) l' then qundup l' else v :: qundup l'
  end.

(* absorb x != v into the bounds when possible *)
Definition absorb (st : option (bool * Q) * option (bool * Q) * seq Q)
    (v : Q) :=
  let: (lo, up, ks) := st in
  match lo with
  | Some (s, c) =>
     if qlt v c || (s && Qeq_bool v c) then (lo, up, ks)
     else if Qeq_bool v c then (Some (true, c), up, ks)
     else match up with
          | Some (s', c') =>
            if qlt c' v || (s' && Qeq_bool v c') then (lo, up, ks)
            else if Qeq_bool v c' then (lo, Some (true, c'), ks)
            else (lo, up, ks ++ [:: v])
          | None => (lo, up, ks ++ [:: v])
          end
  | None =>
     match up with
     | Some (s', c') =>
       if qlt c' v || (s' && Qeq_bool v c') then (lo, up, ks)
       else if Qeq_bool v c' then (lo, Some (true, c'), ks)
       else (lo, up, ks ++ [:: v])
     | None => (lo, up, ks ++ [:: v])
     end
  end.

Definition atom_rconds (fs : seq (rc Q)) (i : nat) : seq rcond :=
  let lo := foldl (best false) None (pmap (low_of i) fs) in
  let up := foldl (best true) None (pmap (upp_of i) fs) in
  let: (lo, up, ks) :=
    foldl absorb (lo, up, [::]) (qundup (pmap (neq_of i) fs)) in
  match lo, up with
  | Some (s1, c1), Some (s2, c2) =>
    if Qeq_bool c1 c2 then [:: RLow s1 (q2b c1) i; RUpp s2 (q2b c2) i]
    else [:: RInt s1 (q2b c1) i s2 (q2b c2)]
  | Some (s, c), None => [:: RLow s (q2b c) i]
  | None, Some (s, c) => [:: RUpp s (q2b c) i]
  | None, None => [::]
  end ++ map (fun v => RNeq i (q2b v)) ks.

(* p scaled so that its non-constant part has coprime integer coefficients *)
Definition lkey (p : poly) : poly := pscale (pcontent (pnc p)) p.

(* 0 <= P: for each non-constant part keep the smallest constant *)
Definition ge_add (ges : seq poly) (P : poly) : seq poly :=
  let kP := lkey P in
  let same R := peqb (pnc (lkey R)) (pnc kP) in
  if has same ges then
    map (fun R => if same R && qlt (pconst_of kP) (pconst_of (lkey R))
                  then P else R) ges
  else ges ++ [:: P].

Definition pundup (ps : seq poly) : seq poly :=
  foldl (fun acc p => if has (peqb p) acc then acc else acc ++ [:: p]) [::] ps.

(* P != 0: dropped when implied by some 0 <= Q, merged when P = +-Q *)
Definition ne_step (st : seq (bool * poly) * seq poly) (P : poly) :=
  let: (ges, nes) := st in
  let same g := peqb g.2 P || peqb g.2 (pscale (-1) P) in
  if has (fun g => rimp1 (KGe, g.2) (KNe, P)) ges then st
  else if has same ges then
    (map (fun g => if same g then (true, g.2) else g) ges, nes)
  else (ges, nes ++ [:: P]).

Definition to_side (p : poly) : side := map (fun t => (q2b t.1, t.2)) p.

(* the display: negative terms and constant on the other side *)
Definition fact_rc (strict : bool) (k : fkind) (P : poly) : rcond :=
  let c := pconst_of P in
  let L := pnc P in
  let pos := filter (fun t => qlt 0 t.1) L in
  let neg := map (fun t => (- t.1, t.2)) (filter (fun t => ~~ qlt 0 t.1) L) in
  let mc := if qz c then [::] else [:: (- c, [::])] in
  match k with
  | KNe => RDiff (to_side pos) (to_side (neg ++ mc))
  | _ =>
    if pos is [::] then
      RCmp strict (to_side neg)
        (to_side (if qz c then [::] else [:: (c, [::])]))
    else RCmp strict (to_side (neg ++ mc)) (to_side pos)
  end.

Definition is_gen (r : rcond) : bool :=
  if r is RCmp _ _ _ then true else if r is RDiff _ _ then true else false.

(* drop the general conditions implied by the other ones *)
Fixpoint prune (done todo : seq rcond) : seq rcond :=
  match todo with
  | [::] => done
  | r :: todo' =>
    if is_gen r && all (fimp (done ++ todo')) (rfacts r) then prune done todo'
    else prune (done ++ [:: r]) todo'
  end.

Definition refine_raw (cs : seq cond) : seq rcond :=
  let fs :=
    map normf (filter (fun f => ~~ ptriv f) (flatten (map facts_of cs))) in
  let olds := pmap old_of fs in
  let gens := filter (fun f => if old_of f is None then true else false) fs in
  let ges := foldl ge_add [::] (map snd (filter is_ge gens)) in
  let nes := pundup (map snd (filter (fun f => ~~ is_ge f) gens)) in
  let: (ges, nes) := foldl ne_step (map (fun P => (false, P)) ges, [::]) nes in
  let atoms := undup (pmap rc_atom olds) in
  prune [::] (flatten (map (atom_rconds olds) atoms) ++
    map (fun g => fact_rc g.1 KGe g.2) ges ++ map (fact_rc false KNe) nes).

Local Close Scope Q_scope.
