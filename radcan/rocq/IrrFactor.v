(******************************************************************************)
(* IrrFactor: factorisation of univariate integer polynomials into            *)
(* irreducibles (Berlekamp mod p, Hensel lifting, Zassenhaus recombination).  *)
(* Nothing here is verified: callers check every result by multiplication.    *)
(* Polynomials are dense lists of Z, lowest degree first, no trailing zero.   *)
(*   zn, zadd, zsub, zmul, zprim == normalisation and arithmetic over Z       *)
(*   zdivZ f g      == exact quotient f / g over Z, if any                    *)
(*   mp_*  m        == arithmetic modulo m (coefficients in [0, m))           *)
(*   berlekamp p f  == monic irreducible factors of f mod p (p prime)         *)
(*   hensel p F g h k == the lift mod p ^ k of the monic factor g of F,       *)
(*                     F = g * h mod p                                        *)
(*   recomb         == Zassenhaus recombination of the lifted factors         *)
(*   ufactor f      == irreducible factors of the square-free f: primitive,   *)
(*                     positive leading coefficient, product = zprim f;       *)
(*                     [:: zprim f] when no good prime is found               *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt ZArith.
From mathcomp Require Import all_boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.

Definition zpoly := seq Z.

(* Arithmetic over Z *)

Fixpoint drop0 (l : seq Z) : seq Z :=
  if l is Z0 :: l' then drop0 l' else l.

Definition zn (p : zpoly) : zpoly := rev (drop0 (rev p)).

Definition zlc (p : zpoly) : Z := last 0 p.

Fixpoint zadd_raw (p q : zpoly) : zpoly :=
  match p, q with
  | [::], _ => q
  | _, [::] => p
  | a :: p', b :: q' => (a + b) :: zadd_raw p' q'
  end.

Definition zadd (p q : zpoly) : zpoly := zn (zadd_raw p q).
Definition zopp (p : zpoly) : zpoly := map Z.opp p.
Definition zsub (p q : zpoly) : zpoly := zadd p (zopp q).
Definition zscale (c : Z) (p : zpoly) : zpoly := zn (map (Z.mul c) p).

Fixpoint zmul (p q : zpoly) : zpoly :=
  if p is a :: p' then zadd (map (Z.mul a) q) (0 :: zmul p' q) else [::].

Definition zshift (k : nat) (p : zpoly) : zpoly :=
  if p is [::] then [::] else nseq k 0 ++ p.

Fixpoint zderiv_aux (i : Z) (p : zpoly) : zpoly :=
  if p is c :: p' then (i * c) :: zderiv_aux (i + 1) p' else [::].

Definition zderiv (p : zpoly) : zpoly := zn (zderiv_aux 1 (behead p)).

Definition zcont (p : zpoly) : Z := foldr Z.gcd 0 p.

(* primitive part with a positive leading coefficient *)
Definition zprim (p : zpoly) : zpoly :=
  let c := zcont p in
  if Z.eqb c 0 then p else
  let c' := if Z.ltb (zlc p) 0 then - c else c in
  map (fun x => Z.div x c') p.

Fixpoint zdiv_loop (fuel : nat) (g q r : zpoly) : option zpoly :=
  match fuel with
  | O => None
  | S f =>
    if r is [::] then Some q else
    if (size r < size g)%N then None else
    let c := zlc r in
    if Z.eqb (Z.modulo c (zlc g)) 0 then
      let t := zshift (size r - size g) [:: Z.div c (zlc g)] in
      zdiv_loop f g (zadd q t) (zsub r (zmul t g))
    else None
  end.

Definition zdivZ (f g : zpoly) : option zpoly :=
  if g is [::] then None else zdiv_loop (size f).+1 g [::] f.

Definition zmaxabs (p : zpoly) : Z := foldr (fun c m => Z.max (Z.abs c) m) 0 p.

(* Arithmetic modulo m *)

Definition mp_red (m : Z) (p : zpoly) : zpoly :=
  zn (map (fun c => Z.modulo c m) p).

Definition mp_add m (p q : zpoly) : zpoly := mp_red m (zadd_raw p q).
Definition mp_sub m (p q : zpoly) : zpoly := mp_red m (zadd_raw p (zopp q)).
Definition mp_mul m (p q : zpoly) : zpoly := mp_red m (zmul p q).
Definition mp_scale m (c : Z) (p : zpoly) : zpoly := mp_red m (map (Z.mul c) p).

(* symmetric representative in (-m/2, m/2] *)
Definition zsym (m : Z) (p : zpoly) : zpoly :=
  zn (map (fun c => let c' := Z.modulo c m in
                    if Z.ltb m (2 * c') then c' - m else c') p).

Fixpoint zpowmod_pos (m c : Z) (e : positive) : Z :=
  match e with
  | xH => Z.modulo c m
  | xO e' => let h := zpowmod_pos m c e' in Z.modulo (h * h) m
  | xI e' => let h := zpowmod_pos m c e' in Z.modulo (h * h * c) m
  end.

(* inverse modulo the prime p (Fermat) *)
Definition zinv (p c : Z) : Z :=
  if p - 2 is Zpos e then zpowmod_pos p c e else Z.modulo c p.

(* division by g modulo m, ilc the inverse of the leading coefficient of g *)
Fixpoint mp_divmod_loop m (g : zpoly) (ilc : Z) (fuel : nat) (q r : zpoly) :=
  match fuel with
  | O => (q, r)
  | S f =>
    if (size r < size g)%N then (q, r) else
    let t := zshift (size r - size g) [:: Z.modulo (zlc r * ilc) m] in
    mp_divmod_loop m g ilc f (mp_add m q t) (mp_sub m r (mp_mul m t g))
  end.

Definition mp_divmod_inv m (ilc : Z) (r g : zpoly) : zpoly * zpoly :=
  mp_divmod_loop m g ilc (size r).+1 [::] r.

(* modulo a prime p *)
Definition mp_divmod p (r g : zpoly) : zpoly * zpoly :=
  mp_divmod_inv p (zinv p (zlc g)) r g.

Definition mp_monic p (a : zpoly) : zpoly :=
  if a is [::] then [::] else mp_scale p (zinv p (zlc a)) a.

Fixpoint mp_gcd_loop p (fuel : nat) (a b : zpoly) : zpoly :=
  match fuel with
  | O => a
  | S f => if b is [::] then a else mp_gcd_loop p f b (mp_divmod p a b).2
  end.

Definition mp_gcd p (a b : zpoly) : zpoly :=
  mp_monic p (mp_gcd_loop p (size a + size b).+1 a b).

(* (g, s, t) with s * a + t * b = g = gcd a b, g monic *)
Fixpoint mp_egcd_loop p (fuel : nat) (r0 r1 s0 s1 t0 t1 : zpoly) :=
  match fuel with
  | O => (r0, s0, t0)
  | S f =>
    if r1 is [::] then (r0, s0, t0) else
    let: (q, r) := mp_divmod p r0 r1 in
    mp_egcd_loop p f r1 r s1 (mp_sub p s0 (mp_mul p q s1))
                 t1 (mp_sub p t0 (mp_mul p q t1))
  end.

Definition mp_egcd p (a b : zpoly) : zpoly * zpoly * zpoly :=
  let: (g, s, t) :=
    mp_egcd_loop p (size a + size b).+1 a b [:: 1] [::] [::] [:: 1] in
  let c := zinv p (zlc g) in
  (mp_scale p c g, mp_scale p c s, mp_scale p c t).

(* x ^ e mod f modulo p, f monic *)
Fixpoint mp_xpow p (f : zpoly) (e : positive) : zpoly :=
  let md := fun a => (mp_divmod_inv p 1 a f).2 in
  match e with
  | xH => md [:: 0; 1]
  | xO e' => let h := mp_xpow p f e' in md (mp_mul p h h)
  | xI e' => let h := mp_xpow p f e' in md (mp_mul p (0 :: mp_mul p h h) [:: 1])
  end.

(* Berlekamp *)

Definition vsub p (u v : seq Z) : seq Z :=
  map (fun xy => Z.modulo (xy.1 - xy.2) p) (zip u v).

Definition vscale p (c : Z) (u : seq Z) : seq Z :=
  map (fun x => Z.modulo (c * x) p) u.

Fixpoint pick_pivot (col : nat) (rows : seq (seq Z)) :=
  match rows with
  | [::] => None
  | r :: rs =>
    if Z.eqb (nth 0 r col) 0 then
      (if pick_pivot col rs is Some (q, o) then Some (q, r :: o) else None)
    else Some (r, rs)
  end.

(* reduced row echelon form modulo p: the (pivot column, row) *)
Fixpoint rref p (fuel n col : nat) (rows : seq (seq Z)) :
  seq (nat * seq Z) :=
  match fuel with
  | O => [::]
  | S f =>
    if (n <= col)%N then [::] else
    match pick_pivot col rows with
    | None => rref p f n col.+1 rows
    | Some (r, others) =>
      let r1 := vscale p (zinv p (nth 0 r col)) r in
      let others' :=
        map (fun s => vsub p s (vscale p (nth 0 s col) r1)) others in
      let res := rref p f n col.+1 others' in
      let r2 :=
        foldl (fun r cr => vsub p r (vscale p (nth 0 r cr.1) cr.2)) r1 res in
      (col, r2) :: res
    end
  end.

Definition find_piv (i : nat) (piv : seq (nat * seq Z)) : option (seq Z) :=
  if filter (fun cr => cr.1 == i) piv is cr :: _ then Some cr.2 else None.

(* basis of the kernel of the n x n matrix A modulo p *)
Definition kernel p (n : nat) (A : seq (seq Z)) : seq (seq Z) :=
  let piv := rref p n.+1 n 0 A in
  let free := filter (fun j => ~~ (j \in map fst piv)) (iota 0 n) in
  map (fun j =>
         map (fun i =>
                if i == j then 1 else
                if find_piv i piv is Some r then Z.modulo (- nth 0 r j) p
                else 0) (iota 0 n)) free.

Definition pad (n : nat) (r : seq Z) : seq Z := take n (r ++ nseq n 0).

(* the rows x ^ (i p) mod f, i < n *)
Fixpoint qrows p (f xp r : zpoly) (k : nat) : seq zpoly :=
  if k is S k' then
    r :: qrows p f xp (mp_divmod_inv p 1 (mp_mul p r xp) f).2 k'
  else [::].

(* nonconstant gcd (u, v - s), s < p *)
Definition split_by p (v u : zpoly) : seq zpoly :=
  if (size u <= 2)%N then [:: u] else
  filter (fun g => (1 < size g)%N)
    (map (fun s => mp_gcd p u (mp_sub p v [:: Z.of_nat s]))
         (iota 0 (Z.to_nat p))).

(* monic irreducible factors of f mod p, f square-free mod p *)
Definition berlekamp p (f : zpoly) : seq zpoly :=
  let fm := mp_monic p (mp_red p f) in
  let n := (size fm).-1 in
  let xp := if p is Zpos e then mp_xpow p fm e else [::] in
  let Q := map (pad n) (qrows p fm xp [:: 1] n) in
  let QI := map (fun ir => vsub p ir.2 (map (fun j => if j == ir.1 then 1
                                                      else 0) (iota 0 n)))
                (zip (iota 0 n) Q) in
  let A := map (fun j => map (fun r => nth 0 r j) QI) (iota 0 n) in
  let B := filter (fun v => (1 < size v)%N) (map zn (kernel p n A)) in
  let k := (size B).+1 in
  foldl (fun fs v => if size fs == k then fs
                     else flatten (map (split_by p v) fs)) [:: fm] B.

(* Hensel lifting of F = g * h mod p, g monic, s g + t h = 1 mod p, from *)
(* mod m to mod m * p ^ fuel                                             *)
Fixpoint hensel_loop p (F s t : zpoly) (fuel : nat) (m : Z) (g h : zpoly) :=
  match fuel with
  | O => g
  | S f =>
    let e := mp_red p (map (fun c => Z.div c m) (zsub F (zmul g h))) in
    let: (q, r) := mp_divmod_inv p 1 (mp_mul p t e) (mp_red p g) in
    let g' := zadd g (zscale m r) in
    let h' := zadd h (zscale m (mp_add p (mp_mul p s e) (mp_mul p q h))) in
    hensel_loop p F s t f (m * p) g' h'
  end.

Definition hensel p (F g h : zpoly) (k : nat) : zpoly :=
  let: (_, s, t) := mp_egcd p g h in hensel_loop p F s t k.-1 p g h.

(* each element with the others *)
Fixpoint picks (T : Type) (l : seq T) : seq (T * seq T) :=
  if l is x :: l' then
    (x, l') :: map (fun yr => (yr.1, x :: yr.2)) (picks l')
  else [::].

(* d-subsets with their complements *)
Fixpoint choose (T : Type) (l : seq T) (d : nat) {struct l} :
  seq (seq T * seq T) :=
  match d, l with
  | O, _ => [:: ([::], l)]
  | S _, [::] => [::]
  | S d', x :: l' =>
    map (fun cr => (x :: cr.1, cr.2)) (choose l' d') ++
    map (fun cr => (cr.1, x :: cr.2)) (choose l' d)
  end.

(* Zassenhaus recombination modulo M *)
Fixpoint try_subsets M (f : zpoly) (cs : seq (seq zpoly * seq zpoly)) :=
  match cs with
  | [::] => None
  | (sub, rest) :: cs' =>
    let P := foldr (mp_mul M) [:: 1] sub in
    let G := zprim (zsym M (mp_mul M [:: zlc f] P)) in
    if zdivZ f G is Some q then Some (G, q, rest) else try_subsets M f cs'
  end.

Fixpoint recomb M (fuel d : nat) (f : zpoly) (gs acc : seq zpoly) :=
  match fuel with
  | O => rcons acc f
  | S fu =>
    if (size gs < d.*2)%N then
      (if (1 < size f)%N then rcons acc (zprim f) else acc)
    else
      match try_subsets M f (choose gs d) with
      | Some (G, q, rest) => recomb M fu d q rest (rcons acc G)
      | None => recomb M fu d.+1 f gs acc
      end
  end.

Definition primes : seq Z :=
  [:: 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43; 47; 53; 59; 61; 67;
      71; 73; 79; 83; 89; 97; 101; 103; 107; 109; 113; 127; 131; 137; 139].

Definition good_prime (f : zpoly) p : bool :=
  ~~ Z.eqb (Z.modulo (zlc f) p) 0 &&
  (size (mp_gcd p (mp_red p f) (mp_red p (zderiv f))) == 1%N).

(* among the first tries good primes, the one with the fewest factors *)
Fixpoint best_prime (f : zpoly) (tries : nat) (ps : seq Z)
  (best : option (Z * seq zpoly)) {struct ps} :=
  match ps, tries with
  | [::], _ | _, O => best
  | p :: ps', S t =>
    if good_prime f p then
      let gs := berlekamp p f in
      let best' := if best is Some (_, bs) then
                     if (size gs < size bs)%N then Some (p, gs) else best
                   else Some (p, gs) in
      if size gs == 1%N then best' else best_prime f t ps' best'
    else best_prime f tries ps' best
  end.

(* smallest k with B < p ^ k *)
Fixpoint lift_exp (p B : Z) (fuel : nat) (m : Z) (k : nat) : nat :=
  match fuel with
  | O => k
  | S f => if Z.ltb B m then k else lift_exp p B f (m * p) k.+1
  end.

Definition ufactor_tries := 3%N.

Definition ufactor (f0 : zpoly) : seq zpoly :=
  let f := zprim (zn f0) in
  if (size f <= 2)%N then (if size f == 2%N then [:: f] else [::]) else
  match best_prime f ufactor_tries primes None with
  | None => [:: f]
  | Some (p, gs) =>
    if (size gs <= 1)%N then [:: f] else
    let n := (size f).-1 in
    let B := 2 * Z.abs (zlc f) * 2 ^ Z.of_nat n * Z.of_nat n.+1 *
             zmaxabs f in
    let k := lift_exp p B 1000 p 1 in
    let M := p ^ Z.of_nat k in
    let lc := Z.modulo (zlc f) p in
    let lifted :=
      map (fun gr => hensel p f gr.1 (mp_mul p [:: lc]
                                       (foldr (mp_mul p) [:: 1] gr.2)) k)
          (picks gs) in
    recomb M (size gs).*2.+2 1 f lifted [::]
  end.

(* Tests (the factors come with a positive leading coefficient) *)

Example uf1 : ufactor [:: -1; 0; 1] = [:: [:: -1; 1]; [:: 1; 1]].
Proof. by vm_compute. Qed.

Example uf2 :
  ufactor [:: -1; 0; 0; 0; 1] = [:: [:: 1; 1]; [:: -1; 1]; [:: 1; 0; 1]].
Proof. by vm_compute. Qed.

Example uf3 : ufactor [:: 4; 0; 0; 0; 1] = [:: [:: 2; 2; 1]; [:: 2; -2; 1]].
Proof. by vm_compute. Qed.

Example uf4 : ufactor [:: -2; 0; 0; 1] = [:: [:: -2; 0; 0; 1]].
Proof. by vm_compute. Qed.

Example uf5 : ufactor [:: -1; 0; 0; 0; 0; 0; 1] =
  [:: [:: -1; 1]; [:: 1; 1; 1]; [:: 1; 1]; [:: 1; -1; 1]].
Proof. by vm_compute. Qed.

Example uf6 : ufactor [:: 1; 0; -10; 0; 1] = [:: [:: 1; 0; -10; 0; 1]].
Proof. by vm_compute. Qed.

Example uf7 : ufactor (zmul [:: 1; 0; 1] [:: 1; 1; 0; 1]) =
  [:: [:: 1; 0; 1]; [:: 1; 1; 0; 1]].
Proof. by vm_compute. Qed.

Example uf8 : ufactor [:: -2; 1; 6] = [:: [:: 2; 3]; [:: -1; 2]].
Proof. by vm_compute. Qed.

(* Swinnerton-Dyer polynomial of sqrt 2, sqrt 3, sqrt 5: irreducible, *)
(* but it splits into linear or quadratic factors modulo every prime   *)
Example uf9 : ufactor [:: 576; 0; -960; 0; 352; 0; -40; 0; 1] =
  [:: [:: 576; 0; -960; 0; 352; 0; -40; 0; 1]].
Proof. by vm_compute. Qed.

Example uf10 : ufactor [:: 2; -4; -6] = [:: [:: -1; 3]; [:: 1; 1]].
Proof. by vm_compute. Qed.
