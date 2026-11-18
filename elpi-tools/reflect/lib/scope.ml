(* Name resolution of a parsed Elpi program, done as Elpi's compiler does it
   (elpi 4.0.0, src/compiler/compiler.ml, modules Scope_Quotation_Macro and
   Flatten):

   - the declarations are first grouped into nested blocks: namespace,
     anonymous block { }, constraint block, the rest of a block after a
     shorten directive, an accumulated file;
   - a block "defines" the predicates and constructors it declares and the
     predicates its rules have as head, and the types it declares;
   - inside namespace foo, a name that the namespace defines is renamed
     foo.name; inside the scope of shorten foo.{ bar }, bar is renamed foo.bar;
   - a name written with a leading dot (.bar) escapes the namespaces.

   The output is the flat list of the declarations, in source order, with
   their names resolved. *)

open Elpi_parser.Ast
module StrSet = Set.Make (String)
module StrMap = Map.Make (String)

(* ------------------------------------------------------------------------ *)
(* The block structure *)

type item =
  | Leaf of Program.decl  (* Clause, Chr, Kind, Type, Pred, TypeAbbreviation, Macro *)
  | Namespace of string * item list
  | Shorten of (string * string) list * item list  (* (full, short) and its scope *)
  | Block of item list
  | Constraint of string list * string list * item list  (* filter, clique, rules *)

let show_func = Func.show

(* [structure decls] groups the flat list of declarations into blocks.
   It returns the items up to the end of the current block, and the
   declarations after its End. *)
let rec structure (decls : Program.decl list) : item list * Program.decl list =
  match decls with
  | [] -> ([], [])
  | Program.End _ :: rest -> ([], rest)
  | Program.Ignored _ :: rest -> structure rest
  | Program.Begin _ :: rest ->
      let inner, rest = structure rest in
      let items, rest = structure rest in
      (Block inner :: items, rest)
  | Program.Namespace (_, name) :: rest ->
      let inner, rest = structure rest in
      let items, rest = structure rest in
      (Namespace (show_func name, inner) :: items, rest)
  | Program.Constraint (_, filter, clique) :: rest ->
      let inner, rest = structure rest in
      let items, rest = structure rest in
      (Constraint (List.map show_func filter, List.map show_func clique, inner) :: items, rest)
  | Program.Shorten (_, directives) :: rest ->
      (* the scope of a shorten directive is the rest of its block *)
      let inner, rest = structure rest in
      let pairs = List.map (fun (full, short) -> (show_func full, show_func short)) directives in
      ([ Shorten (pairs, inner) ], rest)
  | Program.Accumulated (_, files) :: rest ->
      (* accumulate puts { } around the contents of the file *)
      let file_block (f : Program.decl list parser_output) =
        let inner, _ = structure f.ast in
        Block inner
      in
      let items, rest = structure rest in
      (List.map file_block files @ items, rest)
  | (Program.Clause _ | Program.Chr _ | Program.Kind _ | Program.Type _ | Program.Pred _
    | Program.TypeAbbreviation _ | Program.Macro _) as d :: rest ->
      let items, rest = structure rest in
      (Leaf d :: items, rest)

(* ------------------------------------------------------------------------ *)
(* What a block defines *)

(* The head symbols of a rule, read on the syntax (compiler: ast_heads). *)
let rec heads (t : Term.t) : string list =
  match t.it with
  | Term.App ({ it = Term.Const c; _ }, [ hd; _ ]) when Func.equal c Func.rimplf -> heads hd
  | Term.App ({ it = Term.Const c; _ }, args) when Func.equal c Func.andf -> List.concat_map heads args
  | Term.App ({ it = Term.Const c; _ }, _) | Term.Const c ->
      if Func.is_uvar_name c then [] else [ show_func c ]
  | Term.Parens t -> heads t
  | _ -> []

type defs = { preds : StrSet.t; (* predicates and constructors *) types : StrSet.t }

let no_defs = { preds = StrSet.empty; types = StrSet.empty }
let union a b = { preds = StrSet.union a.preds b.preds; types = StrSet.union a.types b.types }
let prefix_name prefix name = prefix ^ "." ^ name
let prepend prefix d =
  { preds = StrSet.map (prefix_name prefix) d.preds; types = StrSet.map (prefix_name prefix) d.types }

let rec defs_of_items items = List.fold_left (fun acc i -> union acc (defs_of_item i)) no_defs items

and defs_of_item = function
  | Leaf (Program.Clause c) -> { no_defs with preds = StrSet.of_list (heads c.body) }
  | Leaf (Program.Type ts) ->
      (* the compiler counts the declared symbols among the types too *)
      let names = StrSet.of_list (List.map (fun (t : _ Type.t) -> show_func t.name) ts) in
      { preds = names; types = names }
  | Leaf (Program.Pred t) ->
      let names = StrSet.singleton (show_func t.name) in
      { preds = names; types = names }
  | Leaf (Program.Kind ks) ->
      { no_defs with types = StrSet.of_list (List.map (fun (k : _ Type.t) -> show_func k.name) ks) }
  | Leaf (Program.TypeAbbreviation ta) -> { no_defs with types = StrSet.singleton (show_func ta.name) }
  | Leaf _ -> no_defs
  | Namespace (prefix, inner) -> prepend prefix (defs_of_items inner)
  | Shorten (pairs, inner) ->
      let shorts = StrSet.of_list (List.map snd pairs) in
      let d = defs_of_items inner in
      { preds = StrSet.diff d.preds shorts; types = StrSet.diff d.types shorts }
  | Block inner | Constraint (_, _, inner) -> defs_of_items inner

(* ------------------------------------------------------------------------ *)
(* Substitutions (compiler: push_subst, push_subst_shorthands) *)

type subst = { path : string list; (* enclosing namespaces *) map : string StrMap.t }

type substs = { on_terms : subst; on_types : subst }

let empty_subst = { path = []; map = StrMap.empty }
let empty_substs = { on_terms = empty_subst; on_types = empty_subst }

let push_namespace extra symbols s =
  let path = s.path @ [ extra ] in
  let map =
    StrSet.fold (fun c m -> StrMap.add c (String.concat "." (path @ [ c ])) m) symbols s.map
  in
  { path; map }

let push_shorthands pairs s =
  let push1 m (full, short) =
    StrMap.add short (match StrMap.find_opt full m with Some f -> f | None -> full) m
  in
  { s with map = List.fold_left push1 s.map pairs }

(* [resolve s name]: the full name of a global [name] *)
let resolve s name =
  if String.length name > 1 && name.[0] = '.' then String.sub name 1 (String.length name - 1)
  else match StrMap.find_opt name s.map with Some full -> full | None -> name

(* ------------------------------------------------------------------------ *)
(* Renaming terms and types *)

let is_macro name = String.length name > 0 && name.[0] = '@'

let rename_type s (ty : 'a TypeExpression.t) : 'a TypeExpression.t =
  let open TypeExpression in
  let name c =
    let n = show_func c in
    if Func.is_uvar_name c then c else Func.from_string (resolve s n)
  in
  let rec aux t =
    let tit =
      match t.tit with
      | TConst c -> TConst (name c)
      | TApp (c, a, args) -> TApp (name c, aux a, List.map aux args)
      | TPred (attr, args, variadic) -> TPred (attr, List.map (fun (m, t) -> (m, aux t)) args, variadic)
      | TArr (a, b) -> TArr (aux a, aux b)
    in
    { t with tit }
  in
  aux ty

(* [rename_term substs t] renames the global constants of [t]; the names
   bound by a lambda, the variables and the macros are left alone. *)
let rename_term ss (t : Term.t) : Term.t =
  let rec aux bound (t : Term.t) : Term.t =
    let it =
      match t.it with
      | Term.Const c ->
          let n = show_func c in
          if Func.is_uvar_name c || StrSet.mem n bound || is_macro n
             || Func.equal c Func.dummyname || Func.equal c Func.spillf
          then t.it
          else Term.Const (Func.from_string (resolve ss.on_terms n))
      | Term.App (hd, args) -> Term.App (aux bound hd, List.map (aux bound) args)
      | Term.Lam (x, xloc, ty, body) ->
          Term.Lam (x, xloc, Option.map (rename_type ss.on_types) ty, aux (StrSet.add (show_func x) bound) body)
      | Term.Cast (t, ty) -> Term.Cast (aux bound t, rename_type ss.on_types ty)
      | Term.Parens t -> Term.Parens (aux bound t)
      | (Term.CData _ | Term.Quoted _) as it -> it
    in
    { t with it }
  in
  aux StrSet.empty t

(* ------------------------------------------------------------------------ *)
(* Resolved declarations *)

(* A declaration with its names resolved; [clique] is the constraint block a
   CHR rule belongs to. *)
type resolved = { decl : Program.decl; clique : string list }

let rename_decl ss (d : Program.decl) : Program.decl =
  let ty_name (t : _ Type.t) = Func.from_string (resolve ss.on_types (show_func t.name)) in
  let sym_name (t : _ Type.t) = Func.from_string (resolve ss.on_terms (show_func t.name)) in
  let rename_sequent (q : Term.t Chr.sequent) =
    Chr.{ eigen = rename_term ss q.eigen; context = rename_term ss q.context;
          conclusion = rename_term ss q.conclusion }
  in
  match d with
  | Program.Clause c -> Program.Clause { c with body = rename_term ss c.body }
  | Program.Type ts ->
      Program.Type (List.map (fun (t : _ Type.t) -> { t with name = sym_name t; ty = rename_type ss.on_types t.ty }) ts)
  | Program.Pred t -> Program.Pred { t with name = sym_name t; ty = rename_type ss.on_types t.ty }
  | Program.Kind ks -> Program.Kind (List.map (fun (k : _ Type.t) -> { k with name = ty_name k }) ks)
  | Program.TypeAbbreviation ta ->
      let rec value = function
        | TypeAbbreviation.Lam (x, l, v) -> TypeAbbreviation.Lam (x, l, value v)
        | TypeAbbreviation.Ty t -> TypeAbbreviation.Ty (rename_type ss.on_types t)
      in
      Program.TypeAbbreviation
        { ta with name = Func.from_string (resolve ss.on_types (show_func ta.name)); value = value ta.value }
  | Program.Chr r ->
      Program.Chr
        { r with to_match = List.map rename_sequent r.to_match;
                 to_remove = List.map rename_sequent r.to_remove;
                 guard = Option.map (rename_term ss) r.guard;
                 new_goal = Option.map rename_sequent r.new_goal }
  | d -> d

(* [flatten items]: the declarations in source order, names resolved *)
let flatten (items : item list) : resolved list =
  let rec block ss clique items = List.concat_map (item ss clique) items
  and item ss clique = function
    | Leaf d -> [ { decl = rename_decl ss d; clique } ]
    | Namespace (prefix, inner) ->
        let d = defs_of_items inner in
        let ss = { on_terms = push_namespace prefix d.preds ss.on_terms;
                   on_types = push_namespace prefix d.types ss.on_types } in
        block ss clique inner
    | Shorten (pairs, inner) ->
        let ss = { on_terms = push_shorthands pairs ss.on_terms;
                   on_types = push_shorthands pairs ss.on_types } in
        block ss clique inner
    | Block inner -> block ss clique inner
    | Constraint (_filter, names, inner) ->
        block ss (List.map (resolve ss.on_terms) names) inner
  in
  block empty_substs [] items

(* [resolve_program p]: the declarations of a parsed file, names resolved *)
let resolve_program (p : Program.t) : resolved list =
  let items, _ = structure p.ast in
  flatten items
