(* ------------------------------------------------------------------------ *)
(* Refinement of the raw side conditions returned by radcan_check            *)
(*                                                                            *)
(*   bound              == (neg, n, d) : bool * nat * nat, the number        *)
(*                         -(n/d) if neg, n/d otherwise (n%:R or n%:R/d%:R)  *)
(*   amono              == seq (rexpr * nat), a product of powers of atoms   *)
(*                         (an atom is any rexpr read as a value: x, sqrt x) *)
(*   side               == seq (bound * amono), a sum of terms c * m, shown  *)
(*                         as  x + 2 * y - 1  (a term with neg is subtracted)*)
(*   rc B               == conditions with bounds in B:                       *)
(*     RRaw c            raw condition c : cond                               *)
(*     RLow s b i        b <= x_i (s = false) or b < x_i (s = true)           *)
(*     RUpp s b i        x_i <= b (s = false) or x_i < b (s = true)           *)
(*     RNeq i b          x_i != b                                             *)
(*     RCmp s l r        l <= r (s = false) or l < r (s = true), l r : side   *)
(*     RDiff l r         l != r                                               *)
(*   rcond              == rc bound (the refined conditions)                  *)
(*   rcond_interp rt env r, all_rconds rt env rs == their meaning             *)
(*   poly               == seq (Q * amono), sparse polynomials over atoms,    *)
(*                         pnorm e is the polynomial of e (checked: pnorm_sound) *)
(*   refine cs          == the refined conditions                             *)
(*   refine_sound       : all_rconds rt env (refine cs) -> all_conds_gen rt env cs *)
(*                                                                            *)
(* refine computes candidate conditions by unverified heuristics:            *)
(*  - a condition is read as a polynomial fact 0 <= P or P != 0; a product   *)
(*    P = A * B (or a monomial c * x^k * y) gives the facts A != 0, B != 0;   *)
(*  - facts true on constants are dropped, the others are divided by their   *)
(*    content (0 <= 2x - 2y becomes 0 <= x - y);                             *)
(*  - an affine fact in one variable becomes a bound (RLow, RUpp, RNeq), per *)
(*    variable only the strongest bounds are kept, x != c merged into bounds;*)
(*  - other facts are grouped by their non-constant part (the weakest        *)
(*    constants are dropped), P != 0 is merged into 0 <= P (giving 0 < P)    *)
(*    or dropped when implied, and printed with the constant and the        *)
(*    negative terms on the other side: y < x, 1 <= x ^+ 2, x != y;           *)
(* then a proved checker verifies that every raw condition follows from a    *)
(* single refined condition (P = a * Q + b, a b : Q with the right signs),   *)
(* or, for e != 0, that each factor of e follows from one; if this check     *)
(* fails, the raw conditions are returned unchanged.                         *)
(* Only reasoning valid in any numFieldType is used (F may be C).            *)
(* ------------------------------------------------------------------------ *)

From Stdlib Require Import BinNums BinPos BinInt ZArith Lia QArith_base Qreduction.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot Syntax Radcan.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ------------------------------------------------------------------------ *)
(* Refined conditions                                                        *)
(* ------------------------------------------------------------------------ *)

Definition bound := (bool * nat * nat)%type.
Definition amono := seq (rexpr * nat).
Definition side := seq (bound * amono).

Inductive rc (B : Type) : Type :=
  | RRaw : cond -> rc B
  | RLow : bool -> B -> nat -> rc B
  | RUpp : bool -> B -> nat -> rc B
  | RNeq : nat -> B -> rc B
  | RCmp : bool -> side -> side -> rc B
  | RDiff : side -> side -> rc B.

Arguments RRaw {B} c.
Arguments RLow {B} s b i.
Arguments RUpp {B} s b i.
Arguments RNeq {B} i b.
Arguments RCmp {B} s l r.
Arguments RDiff {B} l r.

Definition rcond := rc bound.

(* ------------------------------------------------------------------------ *)
(* Polynomials over atoms                                                    *)
(* ------------------------------------------------------------------------ *)

Local Open Scope Q_scope.

Definition qz (a : Q) : bool := Qeq_bool a 0.
Definition qlt (a b : Q) : bool := ~~ Qle_bool b a.

Definition poly := seq (Q * amono).

Fixpoint amono_cmp (m1 m2 : amono) : comparison :=
  match m1, m2 with
  | [::], [::] => Eq
  | [::], _ => Lt
  | _, [::] => Gt
  | (a1, k1) :: m1', (a2, k2) :: m2' =>
    lex (rexpr_cmp a1 a2) (lex (Nat.compare k1 k2) (amono_cmp m1' m2'))
  end.

Fixpoint amono_mul (m1 m2 : amono) {struct m1} : amono :=
  match m1 with
  | [::] => m2
  | (a1, k1) :: m1' =>
    let fix aux (m2 : amono) : amono :=
      match m2 with
      | [::] => m1
      | (a2, k2) :: m2' =>
        match rexpr_cmp a1 a2 with
        | Lt => (a1, k1) :: amono_mul m1' m2
        | Gt => (a2, k2) :: aux m2'
        | Eq => (a1, (k1 + k2)%N) :: amono_mul m1' m2'
        end
      end in aux m2
  end.

Fixpoint padd (p1 p2 : poly) {struct p1} : poly :=
  match p1 with
  | [::] => p2
  | (c1, m1) :: p1' =>
    let fix aux (p2 : poly) : poly :=
      match p2 with
      | [::] => p1
      | (c2, m2) :: p2' =>
        match amono_cmp m1 m2 with
        | Lt => (c1, m1) :: padd p1' p2
        | Gt => (c2, m2) :: aux p2'
        | Eq => let c := Qred (c1 + c2) in
                if qz c then padd p1' p2' else (c, m1) :: padd p1' p2'
        end
      end in aux p2
  end.

Definition psingle (c : Q) (m : amono) : poly := if qz c then [::] else [:: (c, m)].
Definition pconst (c : Q) : poly := psingle c [::].
Definition patom (a : rexpr) : poly := [:: (1, [:: (a, 1%N)])].

Definition pscale (a : Q) (p : poly) : poly :=
  if qz a then [::] else map (fun t => (Qred (a * t.1), t.2)) p.

Definition pmul_t (t : Q * amono) (q : poly) : poly :=
  foldr (fun u acc => padd (psingle (Qred (t.1 * u.1)) (amono_mul t.2 u.2)) acc) [::] q.

Definition pmul (p q : poly) : poly :=
  foldr (fun t acc => padd (pmul_t t q) acc) [::] p.

Definition ppow (p : poly) (k : nat) : poly := iter k (pmul p) (pconst 1).

Fixpoint pnorm (e : rexpr) : poly :=
  match e with
  | RCst z => pconst (Qmake z xH)
  | RAdd a b => padd (pnorm a) (pnorm b)
  | ROpp a => pscale (-1) (pnorm a)
  | RSub a b => padd (pnorm a) (pscale (-1) (pnorm b))
  | RMul a b => pmul (pnorm a) (pnorm b)
  | RPow a k => ppow (pnorm a) k
  | RInv a =>
    match pnorm a with
    | [::] => [::]
    | [:: (c, [::])] => pconst (Qred (Qinv c))
    | _ => patom (RInv a)
    end
  | _ => patom e
  end.

Fixpoint peqb (p q : poly) : bool :=
  match p, q with
  | [::], [::] => true
  | (c1, m1) :: p', (c2, m2) :: q' =>
    Qeq_bool c1 c2 && cmp_eqb (amono_cmp m1 m2) && peqb p' q'
  | _, _ => false
  end.

(* the constant term (always first) and the non-constant part *)
Definition pconst_of (p : poly) : Q := if p is (c, [::]) :: _ then c else 0.
Definition pnc (p : poly) : poly := if p is (_, [::]) :: p' then p' else p.

(* Some (a, b) when P = a * Q + b *)
Definition lrel (P R : poly) : option (Q * Q) :=
  match pnc R, pnc P with
  | (q, _) :: _, (p, _) :: _ =>
    let a := Qred (p / q) in
    let b := Qred (pconst_of P - a * pconst_of R) in
    if peqb P (padd (pscale a R) (pconst b)) then Some (a, b) else None
  | _, _ => None
  end.

(* ------------------------------------------------------------------------ *)
(* Facts and the checker                                                     *)
(* ------------------------------------------------------------------------ *)

(* KGe: 0 <= P, KGt: 0 < P, KNe: P != 0 *)
Inductive fkind := KGe | KGt | KNe.

Definition fact := (fkind * poly)%type.

(* the fact r implies the fact f *)
Definition rimp1 (r f : fact) : bool :=
  let: (kr, R) := r in let: (kp, P) := f in
  if lrel P R is Some (a, b) then
    match kp, kr with
    | KGe, KNe | KGt, KNe => false
    | KGe, _ => Qle_bool 0 a && Qle_bool 0 b
    | KGt, KGt => qlt 0 a && Qle_bool 0 b
    | KGt, KGe => qlt 0 a && qlt 0 b
    | KNe, KNe => qz b && ~~ qz a
    | KNe, KGt => (qlt 0 a && Qle_bool 0 b) || (qlt a 0 && Qle_bool b 0)
    | KNe, KGe => (qlt 0 a && qlt 0 b) || (qlt a 0 && qlt b 0)
    end
  else false.

(* facts true on constants *)
Definition ptriv (f : fact) : bool :=
  let: (k, P) := f in
  if pnc P is [::] then
    let c := pconst_of P in
    match k with KGe => Qle_bool 0 c | KGt => qlt 0 c | KNe => ~~ qz c end
  else false.

Definition b2q (b : bound) : Q :=
  let: (neg, n, d) := b in
  if d is 0%N then 0
  else Qmake (if neg then Z.opp (Z.of_nat n) else Z.of_nat n) (Pos.of_nat d).

Definition q2b (q : Q) : bound :=
  let q := Qred q in
  (Z.ltb (Qnum q) 0, Z.abs_nat (Qnum q), Pos.to_nat (Qden q)).

Definition pvar (i : nat) : poly := patom (RVar i).

Definition mpoly (m : amono) : poly :=
  foldr (fun ak acc => pmul (ppow (patom ak.1) ak.2) acc) (pconst 1) m.

Definition pterm (t : bound * amono) : poly := pmul (pconst (b2q t.1)) (mpoly t.2).

Definition spoly (s : side) : poly := foldr (fun t acc => padd (pterm t) acc) [::] s.

Definition rpoly (r : rcond) : fact :=
  match r with
  | RRaw (CGe0 e) => (KGe, pnorm e)
  | RRaw (CNeq0 e) => (KNe, pnorm e)
  | RLow s b i => (if s then KGt else KGe, padd (pvar i) (pconst (- b2q b)))
  | RUpp s b i => (if s then KGt else KGe, padd (pconst (b2q b)) (pscale (-1) (pvar i)))
  | RNeq i b => (KNe, padd (pvar i) (pconst (- b2q b)))
  | RCmp s l r => (if s then KGt else KGe, padd (spoly r) (pscale (-1) (spoly l)))
  | RDiff l r => (KNe, padd (spoly l) (pscale (-1) (spoly r)))
  end.

Definition fimp (rs : seq rcond) (f : fact) : bool :=
  ptriv f || has (fun r => rimp1 (rpoly r) f) rs.

(* a monomial c * a1^k1 * ... is nonzero when c and the ai are *)
Definition msplit (p : poly) : seq poly :=
  if p is [:: (c, m)] then pconst c :: map (fun ak => patom ak.1) m else [:: p].

(* e is nonzero when all the nzf e are *)
Fixpoint nzf (e : rexpr) : seq poly :=
  match e with
  | RMul a b => nzf a ++ nzf b
  | RPow a _ | ROpp a | RInv a => nzf a
  | _ => msplit (pnorm e)
  end.

Definition implied (rs : seq rcond) (c : cond) : bool :=
  match c with
  | CGe0 e => fimp rs (KGe, pnorm e)
  | CNeq0 e => fimp rs (KNe, pnorm e) || all (fun p => fimp rs (KNe, p)) (nzf e)
  end.

(* ------------------------------------------------------------------------ *)
(* The heuristics (unverified)                                               *)
(* ------------------------------------------------------------------------ *)

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
  | RLow _ _ i | RUpp _ _ i | RNeq i _ => Some i
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
Definition absorb (st : option (bool * Q) * option (bool * Q) * seq Q) (v : Q) :=
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
  let: (lo, up, ks) := foldl absorb (lo, up, [::]) (qundup (pmap (neq_of i) fs)) in
  (if lo is Some (s, c) then [:: RLow s (q2b c) i] else [::]) ++
  (if up is Some (s, c) then [:: RUpp s (q2b c) i] else [::]) ++
  map (fun v => RNeq i (q2b v)) ks.

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
    if pos is [::] then RCmp strict (to_side neg) (to_side (if qz c then [::] else [:: (c, [::])]))
    else RCmp strict (to_side (neg ++ mc)) (to_side pos)
  end.

Definition is_ge (f : fact) : bool := if f.1 is KNe then false else true.

Definition refine_raw (cs : seq cond) : seq rcond :=
  let fs := map normf (filter (fun f => ~~ ptriv f) (flatten (map facts_of cs))) in
  let olds := pmap old_of fs in
  let gens := filter (fun f => if old_of f is None then true else false) fs in
  let ges := foldl ge_add [::] (map snd (filter is_ge gens)) in
  let nes := pundup (map snd (filter (fun f => ~~ is_ge f) gens)) in
  let: (ges, nes) := foldl ne_step (map (fun P => (false, P)) ges, [::]) nes in
  let atoms := undup (pmap rc_atom olds) in
  flatten (map (atom_rconds olds) atoms) ++
  map (fun g => fact_rc g.1 KGe g.2) ges ++ map (fact_rc false KNe) nes.

Definition refine (cs : seq cond) : seq rcond :=
  let rs := refine_raw cs in
  if all (implied rs) cs then rs else map RRaw cs.

Local Close Scope Q_scope.
Local Open Scope ring_scope.

(* ------------------------------------------------------------------------ *)
(* Meaning of the refined conditions                                         *)
(* ------------------------------------------------------------------------ *)

Definition nat2F (F : numFieldType) (n : nat) : F :=
  match n with 0%N => 0 | 1%N => 1 | _ => n%:R end.

Definition bound_interp (F : numFieldType) (b : bound) : F :=
  let: (neg, n, d) := b in
  let v := if Nat.eqb d 1 then nat2F F n else nat2F F n / nat2F F d in
  if neg then - v else v.

Definition babs (b : bound) : bound := let: (_, n, d) := b in (false, n, d).

Section Interp.
Variables (F : numFieldType) (B : Type) (bI : B -> F).
Variables (rt : nat -> F -> F) (env : seq F).

Definition apow (ak : rexpr * nat) : F :=
  let: (a, k) := ak in
  match k with 1%N => rinterp_gen rt env a | _ => rinterp_gen rt env a ^+ k end.

Definition mI (m : amono) : F :=
  if m is ak :: m' then foldl (fun acc ak => acc * apow ak) (apow ak) m' else 1.

(* the absolute value of a term *)
Definition tI (t : bound * amono) : F :=
  let: (c, m) := t in
  if m is [::] then bound_interp F (babs c)
  else if c is (_, 1%N, 1%N) then mI m else bound_interp F (babs c) * mI m.

Definition sideI (s : side) : F :=
  if s is t :: s' then
    foldl (fun acc t => if t.1.1.1 then acc - tI t else acc + tI t)
          (if t.1.1.1 then - tI t else tI t) s'
  else 0.

Definition rc_interp (r : rc B) : Prop :=
  match r with
  | RRaw c => cond_interp_gen rt env c
  | RLow s b i => if s then bI b < nth 0 env i else bI b <= nth 0 env i
  | RUpp s b i => if s then nth 0 env i < bI b else nth 0 env i <= bI b
  | RNeq i b => nth 0 env i != bI b
  | RCmp s l r => if s then sideI l < sideI r else sideI l <= sideI r
  | RDiff l r => sideI l != sideI r
  end.

Fixpoint all_rc (rs : seq (rc B)) : Prop :=
  match rs with
  | [::] => True
  | r :: rs' => if rs' is [::] then rc_interp r else rc_interp r /\ all_rc rs'
  end.

End Interp.

Notation rcond_interp F rt env r := (rc_interp (@bound_interp F) rt env r).
Notation all_rconds F rt env rs := (all_rc (@bound_interp F) rt env rs).

Section Proofs.
Variable F : numFieldType.

Local Arguments Qred : simpl never.
Local Arguments Qplus : simpl never.
Local Arguments Qmult : simpl never.
Local Arguments Qopp : simpl never.
Local Arguments Qinv : simpl never.

Lemma Z2F_ge0 z : Z.le 0 z -> 0 <= Z2F F z.
Proof. by case: z => //= p _; exact: pos2F_ge0. Qed.

Lemma pos2F_gt0 p : 0 < pos2F F p.
Proof. by rewrite lt_def pos2F_neq0 pos2F_ge0. Qed.

Lemma Q2F_ge0 q : Qle 0 q -> 0 <= Q2F (F:=F) q.
Proof.
case: q => n d; rewrite /Qle /Q2F /= Z.mul_1_r => H.
by rewrite divr_ge0 ?pos2F_ge0 ?Z2F_ge0.
Qed.

Lemma Z2F_gt0 z : Z.lt 0 z -> 0 < Z2F F z.
Proof. by case: z => //= p _; exact: pos2F_gt0. Qed.

Lemma Q2F_gt0 q : Qlt 0 q -> 0 < Q2F (F:=F) q.
Proof.
case: q => n d; rewrite /Qlt /Q2F /= Z.mul_1_r => H.
by rewrite divr_gt0 ?pos2F_gt0 ?Z2F_gt0.
Qed.

Lemma Q2F_minus a b : Q2F (F:=F) (Qminus b a) = Q2F b - Q2F a.
Proof. by rewrite /Qminus Q2F_plus Q2F_opp. Qed.

Lemma Q2F_le a b : Qle_bool a b -> Q2F (F:=F) a <= Q2F b.
Proof.
move/Qle_bool_iff => H; rewrite -subr_ge0 -Q2F_minus; apply: Q2F_ge0.
by rewrite -(Qplus_opp_r a); apply: Qplus_le_compat => //; exact: Qle_refl.
Qed.

Lemma Q2F_lt a b : qlt a b -> Q2F (F:=F) a < Q2F b.
Proof.
rewrite /qlt => /negP H.
have {}H : Qlt a b by apply: Qnot_le_lt => /Qle_bool_iff.
rewrite -subr_gt0 -Q2F_minus; apply: Q2F_gt0.
by rewrite -(Qplus_opp_r a); apply: Qplus_lt_le_compat => //; exact: Qle_refl.
Qed.

Lemma Q2F_eqb a b : Qeq_bool a b -> Q2F (F:=F) a = Q2F b.
Proof. by move/Qeq_bool_iff; exact: Q2F_Qeq. Qed.

Lemma Q2F0 : Q2F (F:=F) 0 = 0.
Proof. by rewrite /Q2F /= mul0r. Qed.

Lemma Q2F1 : Q2F (F:=F) 1 = 1.
Proof. by rewrite /Q2F /= pos2F1 divr1. Qed.

Lemma Q2Fm1 : Q2F (F:=F) (Qmake (Zneg xH) xH) = -1.
Proof. by rewrite /Q2F /= pos2F1 divr1. Qed.

Lemma qzP a : qz a -> Q2F (F:=F) a = 0.
Proof. by move/Q2F_eqb ->; rewrite Q2F0. Qed.

Lemma Q2F_eq0 b : Q2F (F:=F) b = 0 -> qz b.
Proof.
case: b => [[|n|n] d]; rewrite /qz /Q2F /= => /eqP; rewrite ?mul0r //.
  by rewrite mulf_eq0 invr_eq0 !(negbTE (pos2F_neq0 _)).
by rewrite mulf_eq0 invr_eq0 oppr_eq0 !(negbTE (pos2F_neq0 _)).
Qed.

Lemma Q2F_neq0 a : ~~ qz a -> Q2F (F:=F) a != 0.
Proof. by apply: contra => /eqP /Q2F_eq0. Qed.

Lemma Q2F_gt0b a : qlt 0 a -> 0 < Q2F (F:=F) a.
Proof. by move/Q2F_lt; rewrite Q2F0. Qed.

Lemma Q2F_lt0b a : qlt a 0 -> Q2F (F:=F) a < 0.
Proof. by move/Q2F_lt; rewrite Q2F0. Qed.

Lemma Q2F_ge0b a : Qle_bool 0 a -> 0 <= Q2F (F:=F) a.
Proof. by move/Q2F_le; rewrite Q2F0. Qed.

Lemma Q2F_le0b a : Qle_bool a 0 -> Q2F (F:=F) a <= 0.
Proof. by move/Q2F_le; rewrite Q2F0. Qed.

Lemma nat2FE n : nat2F F n = n%:R.
Proof. by case: n => [|[]]. Qed.

Lemma bound_interpE b : bound_interp F b = Q2F (b2q b).
Proof.
case: b => [[neg n] [|d]].
  by rewrite /bound_interp /= !nat2FE invr0 mulr0; case: neg; rewrite /Q2F /= ?oppr0 mul0r.
rewrite /bound_interp /b2q /Q2F /= !nat2FE.
have -> : pos2F F (Pos.of_nat d.+1) = d.+1%:R by rewrite /pos2F Nat2Pos.id.
case: d => [|d].
  by case: neg => /=; rewrite ?Z2F_opp Z2F_nat divr1.
by case: neg => /=; rewrite ?Z2F_opp Z2F_nat ?mulNr.
Qed.

Lemma bound_interp_abs b :
  bound_interp F b = if b.1.1 then - bound_interp F (babs b) else bound_interp F (babs b).
Proof. by case: b => [[[] n] d]. Qed.

Variables (rt : nat -> F -> F) (env : seq F).
Local Notation ri := (rinterp_gen rt env).

Definition aeval (m : amono) : F := foldr (fun ak acc => ri ak.1 ^+ ak.2 * acc) 1 m.
Definition peval (p : poly) : F := foldr (fun t acc => Q2F t.1 * aeval t.2 + acc) 0 p.

Lemma amono_cmp_eq m1 m2 : amono_cmp m1 m2 = Eq -> m1 = m2.
Proof.
elim: m1 m2 => [|[a1 k1] m1 IH] [|[a2 k2] m2] //=.
by case/lexP => /rexpr_cmp_eq -> /lexP [/Nat.compare_eq -> /IH ->].
Qed.

Lemma amono_mul_sound m1 m2 : aeval (amono_mul m1 m2) = aeval m1 * aeval m2.
Proof.
elim: m1 m2 => [|[a1 k1] m1 IH1] m2 /=; first by rewrite mul1r.
elim: m2 => [|[a2 k2] m2 IH2] /=; first by rewrite mulr1.
case E : (rexpr_cmp a1 a2) => /=.
- by rewrite IH1 (rexpr_cmp_eq E) exprD mulrACA.
- by rewrite IH1 /= mulrA.
by rewrite IH2 /= mulrCA.
Qed.

Lemma padd_sound p1 p2 : peval (padd p1 p2) = peval p1 + peval p2.
Proof.
elim: p1 p2 => [|[c1 m1] p1 IH1] p2 /=; first by rewrite add0r.
elim: p2 => [|[c2 m2] p2 IH2] /=; first by rewrite addr0.
case E : (amono_cmp m1 m2).
- rewrite -(amono_cmp_eq E); case: ifP => [/qzP|_] /=.
    rewrite Q2F_red Q2F_plus IH1 => H.
    by rewrite addrACA -mulrDl H mul0r add0r.
  by rewrite IH1 Q2F_red Q2F_plus mulrDl addrACA.
- by rewrite /= IH1 /= addrA.
by rewrite /= IH2 /= addrCA.
Qed.

Lemma psingle_sound c m : peval (psingle c m) = Q2F c * aeval m.
Proof.
by rewrite /psingle; case: ifP => [/qzP -> | _] /=; rewrite ?mul0r ?addr0.
Qed.

Lemma pconst_sound c : peval (pconst c) = Q2F c.
Proof. by rewrite psingle_sound /= mulr1. Qed.

Lemma patom_sound a : peval (patom a) = ri a.
Proof. by rewrite /= Q2F1 mul1r expr1 mulr1 addr0. Qed.

Lemma pscale_sound a p : peval (pscale a p) = Q2F a * peval p.
Proof.
rewrite /pscale; case: ifP => [/qzP -> | _] /=; first by rewrite mul0r.
elim: p => [|[c m] p IH] /=; first by rewrite mulr0.
by rewrite IH Q2F_red Q2F_mult mulrDr mulrA.
Qed.

Lemma pmul_t_sound t q : peval (pmul_t t q) = Q2F t.1 * aeval t.2 * peval q.
Proof.
case: t => c m; elim: q => [|[c2 m2] q IH] /=; first by rewrite mulr0.
rewrite padd_sound psingle_sound IH Q2F_red Q2F_mult amono_mul_sound /=.
by rewrite mulrDr; congr (_ + _); rewrite mulrACA.
Qed.

Lemma pmul_sound p q : peval (pmul p q) = peval p * peval q.
Proof.
elim: p => [|t p IH] /=; first by rewrite mul0r.
by rewrite padd_sound pmul_t_sound IH mulrDl.
Qed.

Lemma ppow_sound p k : peval (ppow p k) = peval p ^+ k.
Proof.
elim: k => [|k IH]; first by rewrite expr0 -[ppow p 0]/(pconst 1) pconst_sound Q2F1.
by rewrite /ppow iterS -/(ppow p k) pmul_sound IH exprS.
Qed.

Lemma pnorm_sound e : peval (pnorm e) = ri e.
Proof.
elim: e => [z|i|n p|n e1 IH1|e1 IH1 e2 IH2|e1 IH1|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 k|e1 IH1] /=.
- by rewrite pconst_sound Q2F_Z.
- by rewrite Q2F1 mul1r expr1 mulr1 addr0.
- by rewrite Q2F1 mul1r expr1 mulr1 addr0.
- by rewrite Q2F1 mul1r expr1 mulr1 addr0.
- by rewrite padd_sound IH1 IH2.
- by rewrite pscale_sound IH1 Q2Fm1 mulN1r.
- by rewrite padd_sound pscale_sound IH1 IH2 Q2Fm1 mulN1r.
- by rewrite pmul_sound IH1 IH2.
- by rewrite ppow_sound IH1.
move: IH1; case: (pnorm e1) => [|[c [|a m]] [|t p]] /= <-; rewrite ?Q2F1 ?mul1r ?expr1 ?mulr1 ?addr0 //.
- by rewrite invr0.
by rewrite pconst_sound Q2F_red Q2F_Qinv.
Qed.

Lemma peqb_sound p q : peqb p q -> peval p = peval q.
Proof.
elim: p q => [|[c1 m1] p IH] [|[c2 m2] q] //=.
by case/andP => /andP [/Q2F_eqb -> /cmp_eqbP /amono_cmp_eq ->] /IH ->.
Qed.

Lemma pconst_ofE p : peval p = Q2F (pconst_of p) + peval (pnc p).
Proof.
case: p => [|[c [|a m]] p] /=; rewrite ?Q2F0 ?add0r //.
by rewrite mulr1.
Qed.

Lemma lrel_sound P R a b : lrel P R = Some (a, b) ->
  peval P = Q2F a * peval R + Q2F b.
Proof.
rewrite /lrel; case: (pnc R) => [|[q m] ?] //; case: (pnc P) => [|[p m'] ?] //.
case: ifP => // /peqb_sound -> [<- <-].
by rewrite padd_sound pscale_sound pconst_sound.
Qed.

Definition kI (k : fkind) (v : F) : Prop :=
  match k with KGe => 0 <= v | KGt => 0 < v | KNe => v != 0 end.

Lemma comb_gt0 (A B q : F) : 0 < A -> 0 <= B -> 0 < q -> 0 < A * q + B.
Proof. by move=> A0 B0 q0; rewrite ltr_wpDr // mulr_gt0. Qed.

Lemma comb_gt0' (A B q : F) : 0 < A -> 0 < B -> 0 <= q -> 0 < A * q + B.
Proof. by move=> A0 B0 q0; rewrite ltr_pwDr // mulr_ge0 // ltW. Qed.

Lemma comb_neg (A B q : F) : 0 < - A * q + - B -> A * q + B != 0.
Proof. by rewrite mulNr -opprD oppr_gt0 => /ltr0_neq0. Qed.

Lemma rimp1_sound r f : rimp1 r f -> kI r.1 (peval r.2) -> kI f.1 (peval f.2).
Proof.
case: r f => kr R [kp P] /=.
case E : (lrel P R) => [[a b]|] //; rewrite (lrel_sound E).
case: kp; case: kr => //=.
- by case/andP => /Q2F_ge0b A /Q2F_ge0b B q; rewrite addr_ge0 // mulr_ge0.
- by case/andP => /Q2F_ge0b A /Q2F_ge0b B q; rewrite addr_ge0 // mulr_ge0 // ltW.
- by case/andP => /Q2F_gt0b A /Q2F_gt0b B q; rewrite comb_gt0'.
- by case/andP => /Q2F_gt0b A /Q2F_ge0b B q; rewrite comb_gt0.
- case/orP => /andP [].
    by move=> /Q2F_gt0b A /Q2F_gt0b B q; rewrite lt0r_neq0 // comb_gt0'.
  move=> /Q2F_lt0b A /Q2F_lt0b B q; apply: comb_neg.
  by rewrite comb_gt0' ?oppr_gt0.
- case/orP => /andP [].
    by move=> /Q2F_gt0b A /Q2F_ge0b B q; rewrite lt0r_neq0 // comb_gt0.
  move=> /Q2F_lt0b A /Q2F_le0b B q; apply: comb_neg.
  by rewrite comb_gt0 ?oppr_gt0 ?oppr_ge0.
by case/andP => /qzP -> /Q2F_neq0 A q; rewrite addr0 mulf_neq0.
Qed.

Lemma ptriv_sound f : ptriv f -> kI f.1 (peval f.2).
Proof.
case: f => k P /=; rewrite (pconst_ofE P) /ptriv; case: (pnc P) => //=; rewrite addr0.
by case: k => /=; [exact: Q2F_ge0b|exact: Q2F_gt0b|exact: Q2F_neq0].
Qed.

(* the display *)

Lemma apowE ak : apow rt env ak = ri ak.1 ^+ ak.2.
Proof. by case: ak => a [|[|k]] //=; rewrite expr1. Qed.

Lemma mIE m : mI rt env m = aeval m.
Proof.
case: m => [|ak m] //=; rewrite apowE.
elim: m (ri ak.1 ^+ ak.2) => [|ak' m IH] x /=; first by rewrite mulr1.
by rewrite IH apowE mulrA.
Qed.

Lemma tIE t : (if t.1.1.1 then - tI rt env t else tI rt env t) = bound_interp F t.1 * aeval t.2.
Proof.
case: t => [[[neg n] d] m]; rewrite [_.1.1.1]/= [_.1]/= [_.2]/=.
have -> : tI rt env ((neg, n, d), m) = bound_interp F (false, n, d) * aeval m.
  rewrite /tI; case: m => [|ak m]; first by rewrite mulr1.
  rewrite mIE; case: n => [|[|n]] //; case: d => [|[|d]] //.
  by rewrite /bound_interp /= mul1r.
by case: neg; rewrite /bound_interp /= ?mulNr.
Qed.

Lemma mpoly_sound m : peval (mpoly m) = aeval m.
Proof.
elim: m => [|[a k] m IH]; first by rewrite -[mpoly _]/(pconst 1) pconst_sound Q2F1.
by rewrite -[mpoly _]/(pmul (ppow (patom a) k) (mpoly m)) pmul_sound ppow_sound patom_sound IH.
Qed.

Lemma pterm_sound t : peval (pterm t) = bound_interp F t.1 * aeval t.2.
Proof. by rewrite /pterm pmul_sound pconst_sound -bound_interpE mpoly_sound. Qed.

Lemma sideIE s : sideI rt env s = peval (spoly s).
Proof.
case: s => [|t s] //=; rewrite padd_sound pterm_sound -tIE.
elim: s (if t.1.1.1 then - tI rt env t else tI rt env t) => [|t' s IH] x /=.
  by rewrite addr0.
rewrite IH padd_sound pterm_sound -tIE addrA; congr (_ + _).
by case: (t'.1.1.1).
Qed.

Local Notation rI := (rc_interp (@bound_interp F) rt env).
Local Arguments padd : simpl never.
Local Arguments pvar : simpl never.
Local Arguments pconst : simpl never.
Local Arguments pscale : simpl never.

Lemma rpoly_sound r : rI r -> kI (rpoly r).1 (peval (rpoly r).2).
Proof.
case: r => [[e|e]|s b i|s b i|i b|s l r|l r] /=; rewrite ?pnorm_sound //.
- rewrite padd_sound pconst_sound patom_sound Q2F_opp -bound_interpE.
  by case: s => /=; rewrite ?subr_gt0 ?subr_ge0.
- rewrite padd_sound pconst_sound pscale_sound patom_sound Q2Fm1 mulN1r.
  by rewrite -bound_interpE; case: s => /=; rewrite ?subr_gt0 ?subr_ge0.
- rewrite padd_sound pconst_sound patom_sound Q2F_opp -bound_interpE.
  by rewrite subr_eq0.
- rewrite padd_sound pscale_sound Q2Fm1 mulN1r -!sideIE.
  by case: s => /=; rewrite ?subr_gt0 ?subr_ge0.
by rewrite padd_sound pscale_sound Q2Fm1 mulN1r -!sideIE subr_eq0.
Qed.

Lemma fimp_sound rs f :
  (forall r, List.In r rs -> rI r) -> fimp rs f -> kI f.1 (peval f.2).
Proof.
move=> H /orP [/ptriv_sound //|].
elim: rs H => [|r rs IH] //= H /orP [Hr|Hrs].
  by apply: rimp1_sound Hr _; apply: rpoly_sound; apply: H; left.
by apply: IH Hrs => r0 Hr0; apply: H; right.
Qed.

Lemma msplit_sound (P : pred poly) p :
  (forall q, P q -> peval q != 0) -> all P (msplit p) -> peval p != 0.
Proof.
move=> H; case: p => [|[c m] [|t p]] /=; rewrite ?andbT; try exact: H.
case/andP => /H; rewrite pconst_sound addr0 => c0 Hm.
rewrite mulf_neq0 //; elim: m Hm => [|[a k] m IH] /=; first by rewrite oner_neq0.
case/andP => /H; rewrite patom_sound => a0 /IH m0.
by rewrite mulf_neq0 // expf_neq0.
Qed.

Lemma nzf_sound (P : pred poly) e :
  (forall q, P q -> peval q != 0) -> all P (nzf e) -> ri e != 0.
Proof.
move=> H.
have D e' : all P (msplit (pnorm e')) -> ri e' != 0.
  by move/(msplit_sound H); rewrite pnorm_sound.
elim: e => [z|i|n p|n e1 IH1|e1 IH1 e2 IH2|e1 IH1|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 k|e1 IH1];
  try exact: D.
- by move/IH1; rewrite /= oppr_eq0.
- by rewrite /= all_cat => /andP [/IH1 h1 /IH2 h2]; rewrite mulf_neq0.
- by move/IH1 => h; rewrite /= expf_neq0.
by move/IH1; rewrite /= invr_eq0.
Qed.

Lemma implied_sound rs c :
  (forall r, List.In r rs -> rI r) -> implied rs c -> cond_interp_gen rt env c.
Proof.
move=> H; case: c => e /=.
  by move/(fimp_sound H) => /=; rewrite pnorm_sound.
case/orP; first by move/(fimp_sound H) => /=; rewrite pnorm_sound.
by apply: nzf_sound => q /(fimp_sound H).
Qed.

Lemma all_rcP rs : all_rc (@bound_interp F) rt env rs -> forall r, List.In r rs -> rI r.
Proof.
elim: rs => [|r rs IH] //=; case: rs IH => [|r' rs] IH.
  by move=> h r0 [<-|].
by case=> h1 /IH h2 r0 [<-|/h2].
Qed.

Lemma all_conds_genI cs :
  (forall c, List.In c cs -> cond_interp_gen rt env c) -> all_conds_gen rt env cs.
Proof.
elim: cs => [|c cs IH] //= H; case: cs IH H => [|c' cs] IH H.
  by apply: H; left.
split; first by apply: H; left.
by apply: IH => c0 Hc0; apply: H; right.
Qed.

Lemma all_rc_raw cs :
  all_rc (@bound_interp F) rt env (map RRaw cs) -> all_conds_gen rt env cs.
Proof. by elim: cs => [|c [|c' cs] IH] //= [h1 /IH]. Qed.

End Proofs.

(* ------------------------------------------------------------------------ *)
(* Main theorem and the decision lemmas for the tactic                       *)
(* ------------------------------------------------------------------------ *)

Theorem refine_sound (F : numFieldType) (rt : nat -> F -> F) env cs :
  all_rconds F rt env (refine cs) -> all_conds_gen rt env cs.
Proof.
rewrite /refine; case: ifP => [Ha /all_rcP H|_]; last exact: all_rc_raw.
apply: all_conds_genI.
move: (refine_raw cs) H Ha => rs H.
elim: cs => [|c cs IH] //= /andP[Hc /IH Hcs] c0 [<-|/Hcs] //.
exact: implied_sound H Hc.
Qed.

Lemma all_conds_bridge_back (F : numFieldType) (r : posroot F) env cs :
  all_conds_gen (proot r) env cs -> all_conds r env cs.
Proof. by elim: cs => [|c cs IH] //=. Qed.

Theorem radcan_eq_refined (F : numFieldType) (r : posroot F) (env : seq F)
    e1 e2 cs rcs :
  radcan_check e1 e2 = Some cs -> refine cs = rcs ->
  all_rconds F (proot r) env rcs -> rinterp r env e1 = rinterp r env e2.
Proof.
move=> H Hr Hc; apply: (radcan_eq_cond H); apply: all_conds_bridge_back.
by apply: refine_sound; rewrite Hr.
Qed.

Theorem radcan_eq_refined0 (F : numFieldType) (env : seq F) e1 e2 cs rcs :
  no_root e1 -> no_root e2 -> radcan_check e1 e2 = Some cs -> refine cs = rcs ->
  all_rconds F (fun _ _ => 0) env rcs -> rinterp0 env e1 = rinterp0 env e2.
Proof.
move=> n1 n2 H Hr Hc; apply: (radcan_eq_cond0 n1 n2 H).
by apply: refine_sound; rewrite Hr.
Qed.

(* ------------------------------------------------------------------------ *)
(* Examples                                                                   *)
(* ------------------------------------------------------------------------ *)

Definition X := RVar 0.
Definition Y := RVar 1.
Definition xp1 := RAdd X (RCst 1).
Definition xm1 := RAdd X (RCst (-1)).

(* 0 <= x+1, 0 <= x-1, x-1 != 0  ~>  1 < x *)
Example refine_ex1 : refine [:: CGe0 xp1; CGe0 xm1; CNeq0 xm1] =
  [:: RLow true (false, 1%N, 1%N) 0%N].
Proof. by vm_compute. Qed.

(* 0 <= x  ~>  0 <= x *)
Example refine_ex2 : refine [:: CGe0 X] =
  [:: RLow false (false, 0%N, 1%N) 0%N].
Proof. by vm_compute. Qed.

(* 0 <= x+1, 0 <= x-1  ~>  1 <= x *)
Example refine_ex3 : refine [:: CGe0 xp1; CGe0 xm1] =
  [:: RLow false (false, 1%N, 1%N) 0%N].
Proof. by vm_compute. Qed.

(* x+1 != 0, x-1 != 0  ~>  x != -1, x != 1 *)
Example refine_ex4 : refine [:: CNeq0 xp1; CNeq0 xm1] =
  [:: RNeq 0 (true, 1%N, 1%N); RNeq 0 (false, 1%N, 1%N)].
Proof. by vm_compute. Qed.

(* 0 <= x, 0 <= y  ~>  0 <= x, 0 <= y *)
Example refine_ex5 : refine [:: CGe0 X; CGe0 Y] =
  [:: RLow false (false, 0%N, 1%N) 0%N; RLow false (false, 0%N, 1%N) 1%N].
Proof. by vm_compute. Qed.

(* not affine: 0 <= x*y + 1  ~>  -1 <= x*y *)
Example refine_ex6 : refine [:: CGe0 (RAdd (RMul X Y) (RCst 1))] =
  [:: RCmp false [:: ((true, 1%N, 1%N), [::])]
        [:: ((false, 1%N, 1%N), [:: (RVar 0, 1%N); (RVar 1, 1%N)])]].
Proof. by vm_compute. Qed.

(* 0 <= 3 is dropped *)
Example refine_ex7 : refine [:: CGe0 (RCst 3)] =
  [::].
Proof. by vm_compute. Qed.

(* 0 <= 1-2x, 3x != 0, 2x-1 != 0  ~>  x < 1/2, x != 0 *)
Example refine_ex8 : refine [:: CGe0 (RSub (RCst 1) (RMul (RCst 2) X)); CNeq0 (RMul (RCst 3) X); CNeq0 (RAdd (RMul (RCst 2) X) (RCst (-1)))] =
  [:: RUpp true (false, 1%N, 2%N) 0%N; RNeq 0 (false, 0%N, 1%N)].
Proof. by vm_compute. Qed.

(* 0 <= 3x+2, 0 <= x+2/3 (duplicate bound)  ~>  -2/3 <= x *)
Example refine_ex9 : refine [:: CGe0 (RAdd (RMul (RCst 3) X) (RCst 2)); CGe0 (RAdd X (RMul (RCst 2) (RInv (RCst 3))))] =
  [:: RLow false (true, 2%N, 3%N) 0%N].
Proof. by vm_compute. Qed.
(* several variables (M8) *)
Definition vx : amono := [:: (RVar 0, 1%N)].
Definition vy : amono := [:: (RVar 1, 1%N)].
Definition one : bound := (false, 1%N, 1%N).

(* 0 <= -1*y + x  ~>  y <= x *)
Example refine_ex10 : refine [:: CGe0 (RAdd (RMul (RCst (-1)) Y) X)] =
  [:: RCmp false [:: (one, vy)] [:: (one, vx)]].
Proof. by vm_compute. Qed.

(* x - y != 0  ~>  x != y *)
Example refine_ex11 : refine [:: CNeq0 (RSub X Y)] =
  [:: RDiff [:: (one, vx)] [:: (one, vy)]].
Proof. by vm_compute. Qed.

(* 0 <= 2x - 2y  ~>  y <= x;  0 <= 2x - 2y + 1  ~>  2y - 1 <= 2x *)
Example refine_ex12 : refine [:: CGe0 (RSub (RMul (RCst 2) X) (RMul (RCst 2) Y))] =
  [:: RCmp false [:: (one, vy)] [:: (one, vx)]].
Proof. by vm_compute. Qed.

Example refine_ex12' :
  refine [:: CGe0 (RAdd (RSub (RMul (RCst 2) X) (RMul (RCst 2) Y)) (RCst 1))] =
  [:: RCmp false [:: ((false, 2%N, 1%N), vy); ((true, 1%N, 1%N), [::])]
                 [:: ((false, 2%N, 1%N), vx)]].
Proof. by vm_compute. Qed.

(* x^3 * y != 0  ~>  x != 0, y != 0 *)
Example refine_ex13 : refine [:: CNeq0 (RMul (RPow X 3) Y)] =
  [:: RNeq 0 (false, 0%N, 1%N); RNeq 1 (false, 0%N, 1%N)].
Proof. by vm_compute. Qed.

(* (x-1) * (x+1) != 0  ~>  x != 1, x != -1 *)
Example refine_ex14 :
  refine [:: CNeq0 (RMul (RAdd X (RCst (-1))) (RAdd X (RCst 1)))] =
  [:: RNeq 0 (false, 1%N, 1%N); RNeq 0 (true, 1%N, 1%N)].
Proof. by vm_compute. Qed.

(* 0 <= x^2 - 1, x^2 - 4 != 0  ~>  1 <= x^2, x^2 != 4 *)
Example refine_ex15 :
  refine [:: CGe0 (RSub (RPow X 2) (RCst 1)); CNeq0 (RSub (RPow X 2) (RCst 4))] =
  [:: RCmp false [:: (one, [::])] [:: (one, [:: (RVar 0, 2%N)])];
      RDiff [:: (one, [:: (RVar 0, 2%N)])] [:: ((false, 4%N, 1%N), [::])]].
Proof. by vm_compute. Qed.

(* implied duplicate: 0 <= x - y, 0 <= 2x - 2y + 1, 0 <= x + y  ~>  y <= x, 0 <= x + y *)
Example refine_ex16 :
  refine [:: CGe0 (RSub X Y); CGe0 (RAdd (RSub (RMul (RCst 2) X) (RMul (RCst 2) Y)) (RCst 1));
             CGe0 (RAdd X Y)] =
  [:: RCmp false [:: (one, vy)] [:: (one, vx)];
      RCmp false [::] [:: (one, vx); (one, vy)]].
Proof. by vm_compute. Qed.

(* merge: 0 <= 3 - (x+y), x + y - 3 != 0  ~>  x + y < 3 *)
Example refine_ex17 :
  refine [:: CGe0 (RSub (RCst 3) (RAdd X Y)); CNeq0 (RSub (RAdd X Y) (RCst 3))] =
  [:: RCmp true [:: (one, vx); (one, vy)] [:: ((false, 3%N, 1%N), [::])]].
Proof. by vm_compute. Qed.

(* atoms other than variables: 0 <= sqrt x, sqrt x != 0  ~>  0 < sqrt x *)
Example refine_ex18 : refine [:: CGe0 (RRootE 2 X); CNeq0 (RRootE 2 X)] =
  [:: RCmp true [::] [:: (one, [:: (RRootE 2 (RVar 0), 1%N)])]].
Proof. by vm_compute. Qed.

(* the m1 goal of Tut10: raw 0 <= y + x, 0 <= -1*y + x, -1*y + x != 0
   refined 0 <= x + y, y < x *)
Example refine_ex19 :
  refine [:: CGe0 (RAdd Y X); CGe0 (RAdd (RMul (RCst (-1)) Y) X);
             CNeq0 (RAdd (RMul (RCst (-1)) Y) X)] =
  [:: RCmp false [::] [:: (one, vx); (one, vy)];
      RCmp true [:: (one, vy)] [:: (one, vx)]].
Proof. by vm_compute. Qed.

(* the user's goal sqrt(x^2-1) / sqrt(x-1) = sqrt(x+1) *)
Example radcan_check_ex :
  radcan_check (RMul (RRootE 2 (RSub (RPow X 2) (RCst 1))) (RInv (RRootE 2 (RSub X (RCst 1)))))
               (RRootE 2 (RAdd X (RCst 1))) = Some [:: CGe0 xp1; CGe0 xm1; CNeq0 xm1].
Proof. by vm_compute. Qed.

Lemma refine_example (F : numFieldType) (r : posroot F) (x : F) : 1 < x ->
  rinterp r [:: x]
    (RMul (RRootE 2 (RSub (RPow X 2) (RCst 1))) (RInv (RRootE 2 (RSub X (RCst 1))))) =
  rinterp r [:: x] (RRootE 2 (RAdd X (RCst 1))).
Proof.
move=> x_gt1.
apply: (@radcan_eq_refined F r [:: x] _ _ _ [:: RLow true (false, 1%N, 1%N) 0%N]).
- by vm_compute.
- by vm_compute.
rewrite /=. (* the goal is now  1 < x *)
exact: x_gt1.
Qed.
