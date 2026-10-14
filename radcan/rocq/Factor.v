(* Factorisation of constant radicands.  Every result is checked by         *)
(* multiplication, never trusted.                                            *)
(*   small_primes     == the primes below trial_bound (1000, tunable)         *)
(*   trial ps n       == trial division of n by the primes ps: (l, m) with   *)
(*                       n = prod l * m, m without prime factor in ps        *)
(*   perfect_power m  == (c, k) with m = c ^ k (integer k-th root by Newton) *)
(*   factor p         == small primes, then the perfect power of the        *)
(*                       cofactor (which may be a non-prime base)             *)
(*   cfactor p        == checked factor p (falls back to [:: (p, 1)])         *)
(*   const_basis ps   == pairwise coprime basis (gcd refinement, paper's     *)
(*                       form 2 / Collins) of the cofactors of ps            *)
(*   cb_factor cb p   == p over the small primes and the basis cb             *)
(*   root_cm n l      == proot n (prod b ^+ f) as coefficient * root monomial *)

From Stdlib Require Import BinNums BinPos BinInt ZArith Lia QArith_base Qreduction.
From mathcomp Require Import all_boot all_order all_algebra.
From Radcan Require Import PosRoot PosRootFacts Syntax Backend Mono.
Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* trial division bound: primes below it are removed first *)
Definition trial_bound := 1000%N.

Definition small_primes : seq positive :=
  Eval vm_compute in map Pos.of_nat (filter prime (iota 2 (trial_bound - 2))).

Module FactorF (Import N : NUM).

Include MonoF N.

(* Factorisation (its result is checked, never trusted) *)
Definition i_of_pos (p : positive) : int := i_of_Z (Zpos p).
Definition i_of_nat (k : nat) : int := i_of_Z (Z.of_nat k).

Definition small_primes_i : seq int := map i_of_pos small_primes.

(* (k, n / d ^ k) with k maximal *)
Fixpoint zval (fuel : nat) (n d : int) (k : nat) : nat * int :=
  match fuel with
  | O => (k, n)
  | S f => if i_eqb (i_rem n d) i_zero then zval f (i_div n d) d k.+1 else (k, n)
  end.

(* trial division by the primes ps: n = prod l * m *)
Fixpoint trial (ps : seq int) (n : int) : seq (positive * nat) * int :=
  match ps with
  | [::] => ([::], n)
  | d :: ps' =>
    if i_ltb n (i_mul d d) then
      (if i_eqb n i_one then ([::], n) else ([:: (i_to_pos n, 1%N)], i_one))
    else
      let: (k, n') := zval (i_size n) n d 0 in
      let: (l, m) := trial ps' n' in
      (if k is O then l else (i_to_pos d, k) :: l, m)
  end.

Definition i_powi (x : int) (k : nat) : int := iter k (i_mul x) i_one.

(* integer k-th root of n by Newton's iteration, from above *)
Fixpoint iroot_loop (fuel : nat) (k : nat) (n x : int) : int :=
  match fuel with
  | O => x
  | S f =>
    let y := i_div (i_add (i_mul (i_of_nat k.-1) x) (i_div n (i_powi x k.-1)))
                   (i_of_nat k) in
    if i_ltb y x then iroot_loop f k n y else x
  end.

Definition iroot (k : nat) (n : int) : int :=
  iroot_loop (i_size n).+2 k n (i_pow (xO xH) ((i_size n) %/ k).+1).

(* m = c ^ e: the first exponent k <= ks that works, then recursively *)
Fixpoint perfect_power_loop (fuel : nat) (ks : seq nat) (m : int) : int * nat :=
  match fuel with
  | O => (m, 1%N)
  | S f =>
    let fix try (ks' : seq nat) : int * nat :=
      match ks' with
      | [::] => (m, 1%N)
      | k :: ks'' =>
        let c := iroot k m in
        if i_eqb (i_powi c k) m then
          let: (c', e) := perfect_power_loop f ks c in (c', (e * k)%N)
        else try ks''
      end in try ks
  end.

(* exponents to try: the primes up to the size of m *)
Definition perfect_power (m : int) : int * nat :=
  let s := i_size m in
  perfect_power_loop s [seq Pos.to_nat p | p <- small_primes & (Pos.to_nat p <= s)%N] m.

Definition factor (p : positive) : seq (positive * nat) :=
  let: (l, m) := trial small_primes_i (i_of_pos p) in
  if i_eqb m i_one then l
  else let: (c, e) := perfect_power m in rcons l (i_to_pos c, e).

Definition fprod (l : seq (positive * nat)) : int :=
  foldr (fun bf acc => i_mul (i_pow bf.1 bf.2) acc) i_one l.

(* checked factorisation: falls back to the trivial one *)
Definition cfactor (p : positive) : seq (positive * nat) :=
  let l := factor p in if i_eqb (fprod l) (i_of_pos p) then l else [:: (p, 1%N)].

(* coprime basis by gcd refinement *)
Fixpoint cb_insert (fuel : nat) (a : int) (bs : seq int) : seq int :=
  match fuel with
  | O => a :: bs
  | S f =>
    if i_eqb a i_one then bs else
    match bs with
    | [::] => [:: a]
    | b :: bs' =>
      let g := i_gcd a b in
      if i_eqb g i_one then b :: cb_insert f a bs'
      else cb_insert f (i_div a g) (cb_insert f g (cb_insert f (i_div b g) bs'))
    end
  end.

Definition cb_fuel := 64%N.

Definition const_basis (ps : seq positive) : seq int :=
  foldr (fun p bs => cb_insert cb_fuel (trial small_primes_i (i_of_pos p)).2 bs)
        [::] ps.

(* p over the small primes and the basis cb (to be checked) *)
Definition cb_factor (cb : seq int) (p : positive) : seq (positive * nat) :=
  let: (l, m) := trial small_primes_i (i_of_pos p) in
  let: (l', m') :=
    foldl (fun acc b => let: (l, m) := acc in
                        let: (k, m') := zval (i_size m) m b 0 in
                        (if k is O then l else rcons l (i_to_pos b, k), m'))
          ([::], m) cb in
  if i_eqb m' i_one then l ++ l' else rcons (l ++ l') (i_to_pos m', 1%N).

(* proot n (prod b ^+ f) as coefficient * monomial *)
Definition root_cm (n : nat) (l : seq (positive * nat)) : int * mono :=
  foldr (fun bf acc => let: (c1, m1) := fct_norm bf.1 n bf.2 in
                       let: (c2, m2) := mono_mul m1 acc.2 in
                       (i_mul (i_mul c1 c2) acc.1, m2))
        (i_one, [::]) l.

Local Open Scope ring_scope.

Section FactorSound.

Variable F : numFieldType.
Variable r : posroot F.

Local Notation fct_interp := (fct_interp r).
Local Notation mono_interp := (mono_interp r).

Lemma fprod_sound l : I2F F (fprod l) = \prod_(bf <- l) pos2F F bf.1 ^+ bf.2.
Proof.
elim: l => [|[b f] l IH] /=; first by rewrite big_nil I2F_i_one.
by rewrite big_cons I2F_i_mul I2F_i_pow IH.
Qed.

Lemma cfactor_sound p :
  pos2F F p = \prod_(bf <- cfactor p) pos2F F bf.1 ^+ bf.2.
Proof.
rewrite /cfactor; case: ifP => [/i_eqbP H|_]; last by rewrite big_seq1 expr1.
by rewrite -fprod_sound /I2F H /i_of_pos i_of_ZK.
Qed.

Lemma root_cm_sound n l : (0 < n)%N ->
  I2F F (root_cm n l).1 * mono_interp (root_cm n l).2 =
  proot r n (\prod_(bf <- l) pos2F F bf.1 ^+ bf.2).
Proof.
move=> n0; elim: l => [|[b f] l IH].
  by rewrite big_nil proot_1 //= I2F_i_one mono_interp_nil mulr1.
move: IH; rewrite /root_cm /=; case: (foldr _ _ l) => c0 m0 /= IH.
have := fct_norm_sound r b n f; case: fct_norm => c1 m1 /= H1.
have := mono_mul_sound r m1 m0; case: mono_mul => c2 m2 /= H2.
rewrite big_cons prootM ?exprn_ge0 ?prodr_ge0 ?pos2F_ge0 //; last first.
  by move=> i _; rewrite exprn_ge0 ?pos2F_ge0.
rewrite /= prootX ?pos2F_ge0 // -IH -H1 !I2F_i_mul.
rewrite (mulrAC (I2F F c1) (I2F F c2)) -!mulrA; congr (_ * _).
by rewrite H2 mulrCA.
Qed.

End FactorSound.

End FactorF.
