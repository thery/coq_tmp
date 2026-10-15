(******************************************************************************)
(* MFactorEEZ: stage 3 of multivariate factoring over Z, Wang-style          *)
(* evaluation and multivariate Hensel lifting (EEZ).  Nothing here is         *)
(* verified: callers check every result by multiplication.                    *)
(*   mshift pts f   == f with x_v replaced by x_v + a_v for (v, a_v) in pts   *)
(*   udioph p M k us c == univariate diophantine solution mod M = p ^ k       *)
(*   mdioph ...     == multivariate diophantine solution mod (M, I ^ (d+1))   *)
(*   mhensel ...    == multivariate Hensel lifting with imposed leading       *)
(*                     coefficients (Geddes-Czapor-Labahn, alg. 6.4)          *)
(*   eez rec f      == factors of f (primitive, square-free, no factor of     *)
(*                     degree <= 1 in any variable); rec factors the leading  *)
(*                     coefficient; [:: f] when no good point is found        *)
(*   mfactor_full f == mfactor with eez as a fallback                         *)
(******************************************************************************)

From Stdlib Require Import BinNums BinPos BinInt ZArith.
From mathcomp Require Import all_boot.
From Radcan Require Import IrrFactor MFactor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.

(* Auxiliary operations *)

Definition zsmod (M c : Z) : Z :=
  let c' := Z.modulo c M in if Z.ltb M (2 * c') then c' - M else c'.

(* symmetric reduction modulo M *)
Definition msym (M : Z) (p : mpoly) : mpoly :=
  [seq t | t <- [seq (zsmod M t.1, t.2) | t <- p] & ~~ Z.eqb t.1 0].

(* x_v := 0 *)
Definition mset0 (v : nat) (p : mpoly) : mpoly :=
  [seq t | t <- p & nth 0%N t.2 v == 0%N].

Definition set0s (vs : seq nat) (p : mpoly) : mpoly := foldr mset0 p vs.

(* coefficient of x_v ^ m *)
Definition mcoef (v m : nat) (p : mpoly) : mpoly :=
  [seq (t.1, eset t.2 v 0) | t <- p & nth 0%N t.2 v == m].

Definition mxpow (v m : nat) (p : mpoly) : mpoly :=
  mmul_term (1, eset [::] v m) p.

Definition msum (l : seq mpoly) : mpoly := foldr madd [::] l.

(* leading coefficient in x_v *)
Definition mlcv (v : nat) (p : mpoly) : mpoly := mcoef v (mdeg v p) p.

Definition mshift (pts : seq (nat * Z)) (p : mpoly) : mpoly :=
  if all (fun va => Z.eqb va.2 0) pts then p else
  foldr (fun t acc =>
    madd (foldr (fun va q =>
                   mmul q (mpow (madd (mvar va.1) (mconst va.2))
                                (nth 0%N t.2 va.1)))
                [:: (t.1, etrim (foldr (fun va e => set_nth 0%N e va.1 0%N)
                                       t.2 pts))] pts) acc) [::] p.

Definition meval_pt (pts : seq (nat * Z)) (q : mpoly) : Z :=
  foldr (fun t acc =>
    t.1 * foldr (fun va r => va.2 ^ Z.of_nat (nth 0%N t.2 va.1) * r) 1 pts
    + acc) 0 q.

(* f at the point pts, as a univariate polynomial in x_i *)
Definition mimage (i : nat) (pts : seq (nat * Z)) (f : mpoly) : zpoly :=
  zn (map (meval_pt pts) (to_uni i f)).

(* inverse modulo M = p ^ k (Newton iteration from the inverse mod p) *)
Definition zinvM (p M : Z) (k : nat) (c : Z) : Z :=
  iter k (fun x => Z.modulo (x * (2 - c * x)) M) (zinv p (Z.modulo c p)).

(* Univariate diophantine equations *)

(* sum s_i * prod_{j <> i} u_j = c mod p, deg s_i < deg u_i *)
Fixpoint udp (p : Z) (us : seq zpoly) (c : zpoly) : seq zpoly :=
  match us with
  | [::] => [::]
  | [:: _] => [:: mp_red p c]
  | u :: us' =>
    let W := foldr (mp_mul p) [:: 1] us' in
    let: (_, _, t) := mp_egcd p u W in
    let s1 := (mp_divmod p (mp_mul p t c) u).2 in
    let rest := (mp_divmod p (mp_sub p c (mp_mul p s1 W)) u).1 in
    s1 :: udp p us' rest
  end.

(* the same modulo M = p ^ k, by p-adic lifting *)
Definition udioph (p M : Z) (k : nat) (us : seq zpoly) (c : zpoly) :=
  let usp := map (mp_red p) us in
  let bs := map (fun ur => mp_red M (foldr zmul [:: 1] ur.2)) (picks us) in
  let step (st : seq zpoly * Z) (_ : nat) :=
    let: (sig, pt) := st in
    let e := mp_red M (zsub c (foldr zadd [::]
                                 [seq zmul sb.1 sb.2 | sb <- zip sig bs])) in
    let ds := udp p usp (mp_red p (map (fun x => Z.div x pt) e)) in
    ([seq mp_red M (zadd sd.1 (zscale pt sd.2)) | sd <- zip sig ds], pt * p) in
  (foldl step (map (fun _ => [::]) us, 1) (iota 0 k)).1.

(* Multivariate diophantine equations: sum s_i * prod_{j <> i} u_j = c    *)
(* mod (M, x_v ^ (d + 1) for v in rws), u_i in x_i and the variables rws *)
Fixpoint mdioph (p M : Z) (k : nat) (xi d : nat) (rws : seq nat)
  (us : seq mpoly) (c : mpoly) {struct rws} : seq mpoly :=
  match rws with
  | [::] =>
    map (fun s => msym M (mpoly_of xi s))
        (udioph p M k (map (zpoly_of xi) us) (zpoly_of xi c))
  | v :: rws' =>
    let bs := map (fun ur => msym M (mprod ur.2)) (picks us) in
    let anew := map (mset0 v) us in
    let sig0 := mdioph p M k xi d rws' anew (mset0 v c) in
    let e0 := msym M (msub c (msum [seq mmul sb.1 sb.2 | sb <- zip sig0 bs])) in
    let step (se : seq mpoly * mpoly) (m : nat) :=
      let: (sig, e) := se in
      let cm := mcoef v m e in
      if nilp cm then se else
      let ds := map (mxpow v m) (mdioph p M k xi d rws' anew cm) in
      ([seq msym M (madd sd.1 sd.2) | sd <- zip sig ds],
       msym M (msub e (msum [seq mmul sb.1 sb.2 | sb <- zip ds bs]))) in
    (foldl step (sig0, e0) (iota 1 d)).1
  end.

(* Multivariate Hensel lifting *)

(* replace the leading coefficient in x_i of u by l *)
Definition fixlc (xi : nat) (l u : mpoly) : mpoly :=
  let n := mdeg xi u in madd u (mxpow xi n (msub l (mcoef xi n u))).

(* lift in x_v, the factors U1 being correct modulo x_v *)
Definition hlift_var (p M : Z) (k xi d : nat) (rws : seq nat) (v : nat)
  (Aj : mpoly) (U1 U : seq mpoly) : seq mpoly :=
  let step (Ue : seq mpoly * mpoly) (m : nat) :=
    let: (U, e) := Ue in
    let cm := mcoef v m e in
    if nilp cm then Ue else
    let ds := map (mxpow v m) (mdioph p M k xi d rws U1 cm) in
    let U' := [seq msym M (madd ud.1 ud.2) | ud <- zip U ds] in
    (U', msym M (msub Aj (mprod U'))) in
  (foldl step (U, msym M (msub Aj (mprod U))) (iota 1 (mdeg v Aj))).1.

(* A = prod U mod M, from the univariate factors U0 (in x_i), the leading *)
(* coefficients in x_i of the factors being lcs; the point is 0          *)
Definition mhensel (p M : Z) (k xi d : nat) (A : mpoly) (U0 lcs : seq mpoly)
  (vs : seq nat) : option (seq mpoly) :=
  let steps := [seq (nth 0%N vs i, drop i.+1 vs) | i <- iota 0 (size vs)] in
  let step (st : seq mpoly * seq nat) (va : nat * seq nat) :=
    let: (U, ws) := st in
    let: (v, after) := va in
    let U' := [seq fixlc xi (set0s after ul.2) ul.1 | ul <- zip U lcs] in
    (hlift_var p M k xi d (rev ws) v (set0s after A) U U', rcons ws v) in
  let U := (foldl step (U0, [::]) steps).1 in
  if nilp (msym M (msub A (mprod U))) then Some U else None.

(* EEZ *)

(* a bound on the coefficients of the factors of A *)
Definition mbound (A : mpoly) : Z :=
  let ds := [seq Z.of_nat (mdeg v A) | v <- mvars A] in
  2 ^ (foldr Z.add 0 ds) * foldr (fun d r => (d + 1) * r) 1 ds *
  foldr (fun t m => Z.max (Z.abs t.1) m) 0 A.

(* divide H by the factors cfs of the leading coefficient, when possible *)
Definition mstrip (cfs : seq mpoly) (H : mpoly) : mpoly :=
  foldl (fun H h => if mdiv H h is Some q then q else H) H cfs.

(* the factor G of f, with cofactor q, lifting the split phS * phR of the *)
(* image of f at pts, if any                                             *)
Definition eez_lift (p : Z) (xi : nat) (os : seq nat) (pts : seq (nat * Z))
  (cfs : seq mpoly) (f : mpoly) (phS phR : zpoly) : option (mpoly * mpoly) :=
  let fs := mshift pts f in
  let c := mlcv xi fs in
  let A := mmul c fs in
  let k := lift_exp p (2 * mbound A) 1000 p 1 in
  let M := p ^ Z.of_nat k in
  let ca := const_of (set0s os c) in
  let u ph :=
    mpoly_of xi (zsym M (map (Z.mul (ca * zinvM p M k (zlc ph))) ph)) in
  let d := foldr (fun v m => maxn (mdeg v A) m) 0%N os in
  if mhensel p M k xi d A [:: u phS; u phR] [:: c; c] os is Some (H :: _) then
    let G := mprim (mstrip cfs (mshift [seq (va.1, - va.2) | va <- pts] H)) in
    if (0 < mdeg xi G)%N then
      if mdiv f G is Some q then Some (G, q) else None
    else None
  else None.

Definition zprod (l : seq zpoly) : zpoly := foldr zmul [:: 1] l.

Fixpoint eez_try p xi os pts cfs (f : mpoly)
  (cs : seq (seq zpoly * seq zpoly)) :=
  match cs with
  | [::] => None
  | (Sb, R) :: cs' =>
    if eez_lift p xi os pts cfs f (zprod Sb) (zprod R) is Some (G, q)
    then Some (G, q, R) else eez_try p xi os pts cfs f cs'
  end.

(* recombination: subsets of d image factors, d increasing *)
Fixpoint eez_recomb p xi os pts cfs (fuel d : nat) (f : mpoly)
  (phis : seq zpoly) (acc : seq mpoly) : seq mpoly :=
  let last := if nilp (mvars f) then acc else rcons acc (mprim f) in
  match fuel with
  | O => last
  | S fu =>
    if (size phis < d.*2)%N then last else
    match eez_try p xi os pts cfs f (choose phis d) with
    | Some (G, q, R) => eez_recomb p xi os pts cfs fu d q R (rcons acc G)
    | None => eez_recomb p xi os pts cfs fu d.+1 f phis acc
    end
  end.

(* main variable: constant leading coefficient first, then lowest degree *)
Definition eez_var (f : mpoly) (vs : seq nat) : nat :=
  let score v := (mdeg v f + (if nilp (mvars (mlcv v f)) then 0 else 1000))%N in
  foldl (fun b v => if (score v < score b)%N then v else b) (head 0%N vs) vs.

Definition eez_vals : seq Z :=
  [:: 0; 1; -1; 2; -2; 3; -3; 4; -4; 5; -5; 6; -6; 7; -7].

Definition eez_points (os : seq nat) : seq (seq (nat * Z)) :=
  [seq [seq (vi.2, nth 0 eez_vals ((t + 3 * vi.1) %% size eez_vals))
       | vi <- zip (iota 0 (size os)) os] | t <- iota 0 (size eez_vals)].

Definition good_point (xi : nat) (f : mpoly) (pts : seq (nat * Z)) : bool :=
  let g := mimage xi pts f in
  (size g == (mdeg xi f).+1) && (size (zgcd g (zderiv g)) == 1%N).

(* among the first tries good points, the one with fewest image factors *)
Fixpoint best_point (xi : nat) (f : mpoly) (tries : nat)
  (ps : seq (seq (nat * Z))) (best : option (seq (nat * Z) * seq zpoly))
  {struct ps} :=
  match ps, tries with
  | [::], _ | _, O => best
  | pts :: ps', S t =>
    if good_point xi f pts then
      let gs := ufactor (mimage xi pts f) in
      let best' := if best is Some (_, bs) then
                     if (size gs < size bs)%N then Some (pts, gs) else best
                   else Some (pts, gs) in
      if (size gs <= 1)%N then best' else best_point xi f t ps' best'
    else best_point xi f tries ps' best
  end.

Definition eez_tries := 3%N.

Definition eez (rec : mpoly -> seq mpoly) (f : mpoly) : seq mpoly :=
  let vs := mvars f in
  let xi := eez_var f vs in
  let os := filter (fun v => v != xi) vs in
  match best_point xi f eez_tries (eez_points os) None with
  | None => [:: f]
  | Some (pts, phis) =>
    if (size phis <= 1)%N then [:: f] else
    let img := mimage xi pts f in
    match [seq p <- primes | good_prime img p] with
    | [::] => [:: f]
    | p :: _ =>
      let cfs := [seq h <- rec (mlcv xi f) | ~~ nilp (mvars h)] in
      eez_recomb p xi os pts cfs (size phis) 1 f phis [::]
    end
  end.

Definition mfactor_full (f : mpoly) : seq mpoly :=
  if f is [::] then [:: f] else mfact_with eez (mfuel f) f.

Definition mcheck_full (f : mpoly) : bool :=
  meqb (mprod (mfactor_full f)) (mprim f).
