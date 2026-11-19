(* What elpi-reflect's name resolution (scope.ml) follows, for Elpi 4.0.x;
   chosen by dune (dune: select) when the library elpi.dynload, new in
   Elpi 4.1.0, is absent. *)

(* a block of namespace n sees the names that n declares in that block
   only (compiler.ml, Flatten) *)
let namespace_sees_its_other_blocks = false

(* the name of a signature (pred, func, type/symb) is also a type of the
   block: in namespace n, pred term makes the type term read n.term *)
let signature_names_are_types = true
