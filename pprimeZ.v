From mathcomp Require Import all_ssreflect.

Definition base := 337.
Definition lbase := 
  [:: 2; 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43; 47; 53; 59; 61; 67; 71; 
     73; 79; 83; 89; 97; 101; 103; 107; 109; 113; 127; 131; 137; 139; 149; 151; 
     157; 163; 167; 173; 179; 181; 191; 193; 197; 199; 211; 223; 227; 229; 233; 
     239; 241; 251; 257; 263; 269; 271; 277; 281; 283; 293; 307; 311; 313; 317; 
     331; 337].

Time Compute all prime lbase.

Time Compute all (fun p => prime p == (p \in lbase)) (iota 1 337).

Definition prime1 n := (1 < n) && 
                      all (fun p => (n < p * p) || (~~ (p %| n))) lbase.

Time Compute all prime1 lbase.

Fixpoint pprime_aux n k res := 
  if n is n1.+1 then
      let res1 := if prime1 n && prime1 (k - n) then (n,k-n) :: res else res in
      pprime_aux n1 k res1 
  else res.

Definition pprime k := 
  let l := pprime_aux k./2 k [::] in (size l, l).

Time Compute pprime 10.
Time Compute pprime 100. 
Time Compute pprime 1000.
Time Compute pprime 10000.
Time Compute pprime 100000.

    

Compute 100000 < 337 * 337.
Compute 100020 < 337 * 337.

Compute (iota 1 100000).
Print prime.

