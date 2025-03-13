
Require Import ssreflect ZArith List.

Import ListNotations.

Open Scope Z_scope.

Definition base := 337.

Definition lbase := 
  [ 2; 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43; 47; 53; 59; 61; 67; 71; 
     73; 79; 83; 89; 97; 101; 103; 107; 109; 113; 127; 131; 137; 139; 149; 151; 
     157; 163; 167; 173; 179; 181; 191; 193; 197; 199; 211; 223; 227; 229; 233; 
     239; 241; 251; 257; 263; 269; 271; 277; 281; 283; 293; 307; 311; 313; 317; 
     331; 337].

Fixpoint allb (A : Type) (f : A -> _) l := 
  if l is a :: l1 then andb (f a) (allb A f l1) else true.
Definition prime1 n := andb (1 <? n) 
                      (allb _ (fun p => orb (n <? p * p) (negb ((n mod p) =? 0))) lbase).

Time Compute allb _ prime1 lbase.

Fixpoint pprime_aux n z k res := 
  if n is S n1 then
      let res1 := if andb (prime1 z) (prime1 (k - z)) then (z,k-z) :: res else res in
      pprime_aux n1 (z - 1) k res1 
  else res.

Definition pprime k :=
  let n := k / 2 in  
  let l := pprime_aux (Z.to_nat n) n k [] in (length l, l).

Time Compute pprime 10.
Time Compute pprime 100. 
Time Compute pprime 1000.
Time Compute pprime 10000.
Time Compute pprime 100000.

    