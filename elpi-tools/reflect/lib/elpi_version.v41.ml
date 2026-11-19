(* What elpi-reflect's name resolution (scope.ml) follows, for Elpi >= 4.1.0
   (CHANGES.md of 4.1.0, Language); chosen by dune (dune: select) when the
   library elpi.dynload, new in Elpi 4.1.0, is present. *)

(* a block of namespace n sees all the names n.x declared in the program,
   in any block of n, nested or dotted, also in the files before and in
   the builtins (LPCIC/elpi#346; compiler.ml, Namespaces) *)
let namespace_sees_its_other_blocks = true

(* the name of a signature is not a type: in namespace n, pred term leaves
   the type term as it is *)
let signature_names_are_types = false
