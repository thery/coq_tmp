(******************************************************************************)
(* MGcd: gcd of multivariate integer polynomials (MFactor.mpoly).  Nothing   *)
(* here is verified: every candidate gcd is checked by exact division over Z *)
(* and callers check every use again.                                        *)
(*   mcoprime A B   == cheap test: for each variable v, the gcd modulo a      *)
(*                     small prime of the images of A, B at a point (other   *)
(*                     variables evaluated, leading coefficient of A in v    *)
(*                     non zero) is constant; true means gcd (A, B) in Z     *)
(*   mgcd_heu n A B == the heuristic GCDHEU (Char, Geddes, Gonnet): evaluate *)
(*                     the main variable at an integer xi >= 2 min (|A|,     *)
(*                     |B|) + 2, gcd of the images (recursively, integer gcd *)
(*                     at the bottom), candidate rebuilt from the symmetric  *)
(*                     xi-adic digits, kept if it divides A and B (it is     *)
(*                     then the gcd); at most heu_tries values of xi, gives  *)
(*                     up beyond 2 ^ heu_bits                                *)
(*   mgcd A B       == Some g, g = gcd (A, B) with its integer content and a *)
(*                     positive leading coefficient, or None                 *)
(* A modular algorithm would avoid the big integers, but residues on Stdlib  *)
(* Z are slow under vm_compute and primitive integers would add axioms to    *)
(* the main theorems.                                                        *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt ZArith.
From mathcomp Require Import all_boot.
From Radcan Require Import IrrFactor MFactor MFactorEEZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.

Definition mnormi (p : mpoly) : Z :=
  foldr (fun t m => Z.max (Z.abs t.1) m) 0 p.

(* x_v := c *)
Definition meval_var (v : nat) (c : Z) (p : mpoly) : mpoly :=
  let pw := foldr (fun _ acc => if acc is x :: _ then c * x :: acc else [:: 1])
                  [::] (iota 0 (mdeg v p).+1) in
  let pw := rev pw in
  mnorm (map (fun t => (t.1 * nth 1 pw (nth 0%N t.2 v), eset t.2 v 0)) p).

Fixpoint zdigits_loop (fuel : nat) (xi c : Z) : seq Z :=
  match fuel with
  | O => [::]
  | S f => if Z.eqb c 0 then [::] else
           let d := zsmod xi c in d :: zdigits_loop f xi (Z.div (c - d) xi)
  end.

Definition zdigits (xi c : Z) : seq Z :=
  zdigits_loop (Z.to_nat (Z.log2 (Z.abs c))).+2 xi c.

Definition mgenpoly (v : nat) (xi : Z) (g : mpoly) : mpoly :=
  mnorm (flatten (map (fun t =>
    let ds := zdigits xi t.1 in
    map (fun kd => (kd.2, eset t.2 v kd.1)) (zip (iota 0 (size ds)) ds)) g)).

(* give up when xi ^ deg exceeds 2 ^ heu_bits *)
Definition heu_bits := 5000.
Definition heu_tries := 6%N.

(* positive leading coefficient *)
Definition msgn (P : mpoly) : mpoly := if Z.ltb (mlc P) 0 then mopp P else P.

Definition mdivides (A G : mpoly) : bool :=
  if mdiv A G is Some _ then true else false.

Fixpoint mgcd_heu (fuel : nat) (A B : mpoly) : option mpoly :=
  match fuel with
  | O => None
  | S f =>
    if A is [::] then Some (msgn B) else
    if B is [::] then Some (msgn A) else
    let c := Z.gcd (mcont A) (mcont B) in
    let vs := mvars (A ++ B) in
    if vs is [::] then Some (mconst c) else
    let v := last 0%N vs in
    let A1 := mprim A in
    let B1 := mprim B in
    let d := Z.of_nat (maxn (mdeg v A1) (mdeg v B1)) in
    let fix loop (k : nat) (xi : Z) : option mpoly :=
      match k with
      | O => None
      | S k' =>
        if Z.ltb heu_bits (Z.log2 xi * d) then None else
        match mgcd_heu f (meval_var v xi A1) (meval_var v xi B1) with
        | Some g =>
          let G := mprim (mgenpoly v xi g) in
          if mvars G is [::] then Some (mconst c) else
          if mdivides A1 G && mdivides B1 G then Some (mscale c G)
          else loop k' (Z.div (xi * 73794) 27011)
        | None => loop k' (Z.div (xi * 73794) 27011)
        end
      end in
    loop heu_tries (2 * Z.min (mnormi A1) (mnormi B1) + 2)
  end.

(* Coprimality pre-test.  If the leading coefficient of A in x_v does not
   vanish at the point pts nor modulo p, the degree in x_v of gcd (A, B) is
   at most that of the gcd modulo p of the images at pts: when all these
   are 0, the gcd is a constant.  The gcd modulo p uses pseudo-remainders
   (no modular inverse). *)
Definition cop_prime := 10007.

Fixpoint mp_prem_loop (p : Z) (fuel : nat) (a b : zpoly) : zpoly :=
  match fuel with
  | O => a
  | S f =>
    if (size a < size b)%N then a else
    mp_prem_loop p f (mp_sub p (mp_scale p (zlc b) a)
                           (mp_mul p (zshift (size a - size b) [:: zlc a]) b))
                 b
  end.

Fixpoint mp_pgcd_loop (p : Z) (fuel : nat) (a b : zpoly) : zpoly :=
  match fuel with
  | O => a
  | S f => if b is [::] then a else
           mp_pgcd_loop p f b (mp_prem_loop p (size a).+1 a b)
  end.

(* a gcd modulo p, up to a constant factor *)
Definition mp_pgcd (p : Z) (a b : zpoly) : zpoly :=
  mp_pgcd_loop p (size a + size b).+1 a b.

Definition cop_points (s : nat) (v : nat) (vs : seq nat) : seq (nat * Z) :=
  [seq (j, Z.of_nat (2 * j + 3 + 5 * s)) | j <- vs & j != v].

Definition coprime_at (A B : mpoly) (v : nat) (pts : seq (nat * Z)) :
  option bool :=
  let a := mp_red cop_prime (mimage v pts A) in
  if size a != (mdeg v A).+1 then None else
  let b := mp_red cop_prime (mimage v pts B) in
  Some (size (mp_pgcd cop_prime a b) <= 1)%N.

Definition coprime_var (A B : mpoly) (vs : seq nat) (v : nat) : bool :=
  if (mdeg v A == 0)%N || (mdeg v B == 0)%N then true else
  let fix tries (n : nat) :=
    if n is S n' then
      if coprime_at A B v (cop_points n v vs) is Some r then r
      else tries n'
    else false in
  tries 3%N.

Definition mcoprime (A B : mpoly) : bool :=
  let vs := mvars (A ++ B) in all (coprime_var A B vs) vs.

Definition mgcd (A B : mpoly) : option mpoly :=
  if A is [::] then Some (msgn B) else
  if B is [::] then Some (msgn A) else
  if mcoprime A B then Some (mconst (Z.gcd (mcont A) (mcont B))) else
  mgcd_heu (size (mvars (A ++ B))).+1 A B.
