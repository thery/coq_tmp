(* Polynomial radicands: exact division (unverified, results always         *)
(* checked by the callers), decomposition over a basis, and the Collins-style *)
(* basis of the radicands of a goal (elements with a positive leading        *)
(* coefficient, normsign in Inverse.v), neg_hints (preferred signs of      *)
(* bases, M6).                                                               *)

From Stdlib Require Import BinNums BinPos BinInt ZArith Lia QArith_base Qreduction.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts Syntax Backend Mono Factor NF Inverse.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module PolyF (Import N : NUM).

Include InverseF N.

(* ------------------------------------------------------------------------ *)
(* Exact polynomial division (unverified, results are always checked)        *)
(* ------------------------------------------------------------------------ *)

Definition ispoly (p : nf) : bool := all (fun t => nilp t.2.2) p.

Fixpoint vdiv (v w : vmono) {struct v} : option vmono :=
  match w with
  | [::] => Some v
  | (b, l) :: w' =>
    match v with
    | [::] => None
    | (a, k) :: v' =>
      match atom_cmp a b with
      | Eq => if (l <= k)%N then
                (if vdiv v' w' is Some u then
                   Some (if k == l then u else (a, (k - l)%N) :: u) else None)
              else None
      | Lt => if vdiv v' w is Some u then Some ((a, k) :: u) else None
      | Gt => None
      end
    end
  end.

Fixpoint pdiv_loop (fuel : nat) (p b q : nf) : option nf :=
  match fuel with
  | O => None
  | S f =>
    if p is [::] then Some q else
    match lead p, lead b with
    | Some (c, v), Some (cb, vb) =>
      if vdiv v vb is Some u then
        let t := [:: (c_div c cb, (u, [::]))] in
        pdiv_loop f (nf_add p (nf_opp (nf_mul t b))) b (nf_add q t)
      else None
    | _, _ => None
    end
  end.

Definition pdiv (p b : nf) : option nf :=
  if ispoly p && ispoly b then pdiv_loop 256 p b [::] else None.

Definition const_of (p : nf) : option coef :=
  match p with
  | [::] => Some c_zero
  | [:: (c, ([::], [::]))] => Some c
  | _ => None
  end.

Definition isconst (p : nf) : bool := if const_of p is Some _ then true else false.

Fixpoint dec_one (fuel : nat) (p b : nf) (k : nat) : nat * nf :=
  match fuel with
  | O => (k, p)
  | S f => if pdiv p b is Some q then dec_one f q b k.+1 else (k, p)
  end.

(* p = rem * prod B ^ k  (to be checked) *)
Definition decompose (bs : seq nf) (p : nf) : nf * seq (nf * nat) :=
  foldl (fun acc b => let: (p, l) := acc in
                      let: (k, p') := if isconst b then (0%N, p) else dec_one 32 p b 0 in
                      (p', if k is O then l else rcons l (b, k)))
        (p, [::]) bs.

(* Basis of radicands: primitive, normsign (Inverse.v) and below            *)

(* ------------------------------------------------------------------------ *)
(* Polynomial gcd and square-free decomposition (M7).  Unverified: the       *)
(* basis only guides decompose, whose result is checked by multiplication,   *)
(* and the cancellations using a gcd check both products.                   *)
(* A polynomial is an nf without root monomials; its atoms (variables,      *)
(* inverse atoms, roots of expressions) are the indeterminates.             *)
(*   pgcd f p q  == gcd of p and q over Q (recursive: main atom, content,   *)
(*                  primitive pseudo-remainder sequence), primitive with a   *)
(*                  positive leading coefficient                             *)
(*   sqf f p     == the square-free factors of p (Yun's algorithm in the    *)
(*                  main atom, recursively on the content)                   *)
(*   pb_insert   == insertion in a coprime basis (Collins: A, B become       *)
(*                  gcd, A / gcd, B / gcd)                                   *)
(* ------------------------------------------------------------------------ *)

Definition atom_eqb (a b : atom) : bool := cmp_eqb (atom_cmp a b).

Definition patoms (p : nf) : seq atom :=
  foldr (fun t acc => foldr (fun ak acc => if has (atom_eqb ak.1) acc then acc
                                           else ak.1 :: acc) acc t.2.1) [::] p.

Fixpoint vexp (a : atom) (v : vmono) : nat :=
  match v with
  | [::] => 0%N
  | (b, k) :: v' => if atom_eqb a b then k else vexp a v'
  end.

Definition vremove (a : atom) (v : vmono) : vmono :=
  filter (fun bk => ~~ atom_eqb a bk.1) v.

(* degree in a, coefficient of a ^ k *)
Definition pdeg (a : atom) (p : nf) : nat := foldr (fun t m => maxn (vexp a t.2.1) m) 0%N p.

Definition pcoef (a : atom) (k : nat) (p : nf) : nf :=
  foldr (fun t acc => if vexp a t.2.1 == k then nf_add [:: (t.1, (vremove a t.2.1, t.2.2))] acc
                      else acc) [::] p.

Definition pmono (a : atom) (k : nat) : nf := [:: (c_one, (vsingle a k, [::]))].

Definition psub (p q : nf) : nf := nf_add p (nf_opp q).

Definition pderiv (a : atom) (p : nf) : nf :=
  foldr (fun t acc => let k := vexp a t.2.1 in
                      if k is S k' then
                        nf_add (nf_single (c_mul (c_of_Z (Z.of_nat k)) t.1)
                                          (vmono_mul (vsingle a k') (vremove a t.2.1), t.2.2))
                               acc
                      else acc) [::] p.

Definition pexdiv (p q : nf) : nf := if pdiv p q is Some s then s else p.

Definition pnormal (p : nf) : nf :=
  if p is [::] then [::] else if isconst p then nf_one else normsign (primitive p).

(* pseudo-remainder of A by B in a *)
Definition prem (a : atom) (A B : nf) : nf :=
  let dB := pdeg a B in
  let lB := pcoef a dB B in
  let fix loop (n : nat) (A : nf) : nf :=
    match n with
    | O => A
    | S n' =>
      if A is [::] then A else
      let dA := pdeg a A in
      if (dA < dB)%N then A else
      loop n' (psub (nf_mul lB A) (nf_mul (nf_mul (pcoef a dA A) (pmono a (dA - dB))) B))
    end in
  loop (pdeg a A).+1 A.

Fixpoint pgcd (fuel : nat) (p q : nf) : nf :=
  match fuel with
  | O => nf_one
  | S f =>
    if p is [::] then pnormal q else
    if q is [::] then pnormal p else
    if isconst p || isconst q then nf_one else
    if patoms (p ++ q) is a :: _ then
      let content := fun s => foldr (fun k acc => pgcd f (pcoef a k s) acc) [::]
                                    (iota 0 (pdeg a s).+1) in
      let ppart := fun s => pnormal (pexdiv s (content s)) in
      let fix prs (n : nat) (A B : nf) : nf :=
        match n with
        | O => nf_one
        | S n' =>
          if B is [::] then pnormal A else
          if pdeg a B is O then nf_one else
          prs n' B (ppart (prem a A B))
        end in
      let cp := content p in
      let cq := content q in
      let pp := pexdiv p cp in
      let qq := pexdiv q cq in
      let g := if (pdeg a pp < pdeg a qq)%N then prs (pdeg a qq).+2 qq pp
               else prs (pdeg a pp).+2 pp qq in
      pnormal (nf_mul (pgcd f cp cq) g)
    else nf_one
  end.

Definition gcd_fuel := 32%N.

(* Yun's algorithm in a: the non-constant a_i of p = c * prod a_i ^ i *)
Definition yun (a : atom) (p : nf) : seq nf :=
  let p' := pderiv a p in
  let g := pgcd gcd_fuel p p' in
  let fix loop (n : nat) (b d : nf) : seq nf :=
    match n with
    | O => [::]
    | S n' =>
      if isconst b then [::] else
      let ai := pgcd gcd_fuel b d in
      let b' := pexdiv b ai in
      let c' := pexdiv d ai in
      (if isconst ai then [::] else [:: ai]) ++ loop n' b' (psub c' (pderiv a b'))
    end in
  let b := pexdiv p g in
  loop (pdeg a p).+1 b (psub (pexdiv p' g) (pderiv a b)).

Fixpoint sqf (fuel : nat) (p : nf) : seq nf :=
  match fuel with
  | O => [::]
  | S f =>
    if isconst p || ~~ ispoly p then [::] else
    if patoms p is a :: _ then
      let c := foldr (fun k acc => pgcd gcd_fuel (pcoef a k p) acc) [::]
                     (iota 0 (pdeg a p).+1) in
      sqf f c ++ yun a (pexdiv p c)
    else [::]
  end.

(* insertion in a coprime basis *)
Fixpoint pb_insert (fuel : nat) (a : nf) (bs : seq nf) : seq nf :=
  match fuel with
  | O => bs
  | S f =>
    if isconst a then bs else
    match bs with
    | [::] => [:: a]
    | b :: bs' =>
      let g := pgcd gcd_fuel a b in
      if isconst g then b :: pb_insert f a bs'
      else
        let bg := pnormal (pexdiv b g) in
        let ag := pnormal (pexdiv a g) in
        (* b divides a: b stays in place; otherwise b / g takes its place *)
        if isconst bg then b :: pb_insert f ag bs'
        else pb_insert f ag (pb_insert f g (bg :: bs'))
    end
  end.

(* p / d = p' / d' with p = p' * g and d = d' * g, g a non-constant gcd     *)
(* (to be checked)                                                           *)
Definition gcd_split (p d : nf) : option (nf * nf * nf) :=
  if ispoly p && ispoly d then
    let g := pgcd gcd_fuel p d in
    if isconst g then None else
    if pdiv d g is Some d' then
      if pdiv p g is Some p' then Some (g, p', d') else None
    else None
  else None.

Fixpoint radicands (e : rexpr) : seq rexpr :=
  match e with
  | RRootE _ a => a :: radicands a
  | RAdd a b | RSub a b | RMul a b => radicands a ++ radicands b
  | ROpp a | RPow a _ | RInv a => radicands a
  | _ => [::]
  end.

Fixpoint mfactors (e : rexpr) : seq rexpr :=
  match e with
  | RMul a b => mfactors a ++ mfactors b
  | RPow a _ => mfactors a
  | _ => [:: e]
  end.

Definition atoms_of (p : nf) : seq nf :=
  flatten (map (fun t => map (fun ak => [:: (c_one, ([:: (ak.1, 1%N)], [::]))]) t.2.1) p).

(* the basis: coprime square-free polynomials built from the radicands of    *)
(* the goal, their factors and their atoms                                   *)
Definition mk_basis (es : seq rexpr) : seq nf :=
  let rs := flatten (map radicands es) in
  let ps := map pnorm rs in
  let fs := map pnorm (flatten (map mfactors rs)) in
  foldl (fun bs p => foldl (fun bs a => pb_insert 64 (pnormal a) bs) bs (sqf 16 p))
        [::] (flatten (map atoms_of ps) ++ fs ++ ps).

(* M6: the radicands (and their factors) of the goal with a negative leading *)
(* coefficient, made primitive: hints for the choice of the sign of a base  *)
Definition neg_hints (es : seq rexpr) : seq nf :=
  let rs := flatten (map radicands es) in
  let ps := map (fun e => primitive (pnorm e)) (rs ++ flatten (map mfactors rs)) in
  filter (fun p => if lead p is Some (c, _) then c_neg c else false) ps.

End PolyF.
