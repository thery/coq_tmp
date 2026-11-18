(* From parsed Elpi files to the facts of reflect.elpi (see README.md). *)

open Elpi_parser.Ast
module StrSet = Scope.StrSet

(* Problems that do not stop the reflection (a rule that cannot be
   reflected, a :before naming no rule ...): printed on stderr. *)
let warn loc fmt =
  Printf.ksprintf (fun s -> Printf.eprintf "elpi-reflect: %s: %s\n%!" (Loc.show loc) s) fmt

(* ------------------------------------------------------------------------ *)
(* Locations and attributes *)

let srcloc (l : Loc.t) =
  Printf.sprintf "(reflect.srcloc %s %d %d)" (Print.string_literal l.source_name) l.line
    (l.source_start - l.line_starts_at)

let attribute_data = function
  | Name s -> Some ("(reflect.named " ^ Print.string_literal s ^ ")")
  | Before s -> Some ("(reflect.insert-before " ^ Print.string_literal s ^ ")")
  | After s -> Some ("(reflect.insert-after " ^ Print.string_literal s ^ ")")
  | Replace s -> Some ("(reflect.replaces " ^ Print.string_literal s ^ ")")
  | If s -> Some ("(reflect.if-defined " ^ Print.string_literal s ^ ")")
  | Untyped -> Some "reflect.no-typecheck"
  | AutoSpill -> Some "reflect.auto-spill"
  | _ -> None

(* A rule is kept unless it is under :if "VAR" with VAR not defined *)
let enabled defines attrs =
  List.for_all (function If v -> StrSet.mem v defines | _ -> true) attrs

let name_of attrs = List.find_map (function Name s -> Some s | _ -> None) attrs

(* ------------------------------------------------------------------------ *)
(* Rules *)

type rule = {
  pred : string;  (* the resolved head symbol *)
  loc : Loc.t;
  attrs : raw_attribute list;
  head : Term.t;
  body : Term.t;
}

let true_goal loc = { Term.it = Term.Const Func.truef; loc }

let split_rule (t : Term.t) : Term.t * Term.t =
  let rec strip (t : Term.t) = match t.it with Term.Parens u -> strip u | _ -> t in
  match (strip t).it with
  | Term.App ({ it = Term.Const c; _ }, [ h; b ]) when Func.equal c Func.rimplf -> (h, b)
  | _ -> (t, true_goal t.loc)

let rec head_symbol (t : Term.t) =
  match t.it with
  | Term.App ({ it = Term.Const c; _ }, _) | Term.Const c when not (Func.is_uvar_name c) -> Some (Func.show c)
  | Term.Parens u -> head_symbol u
  | _ -> None

(* The head patterns uvar and (P as X) become reflect.uvar-pattern and
   reflect.as-pattern P X (in a fact they would match) *)
let rec data_of_pattern (t : Term.t) : Term.t =
  let it =
    match t.it with
    | Term.Const c when Func.show c = "uvar" -> Term.Const (Func.from_string "reflect.uvar-pattern")
    | Term.App ({ it = Term.Const c; loc }, [ p; x ]) when Func.equal c Func.asf ->
        Term.App ({ it = Term.Const (Func.from_string "reflect.as-pattern"); loc },
                  [ data_of_pattern p; data_of_pattern x ])
    | Term.App (hd, args) -> Term.App (data_of_pattern hd, List.map data_of_pattern args)
    | Term.Lam (x, l, ty, b) -> Term.Lam (x, l, ty, data_of_pattern b)
    | Term.Cast (u, ty) -> Term.Cast (data_of_pattern u, ty)
    | Term.Parens u -> Term.Parens (data_of_pattern u)
    | it -> it
  in
  { t with it }

(* The lambdas of a term, in textual order: (name, type annotation) *)
let rec binders (t : Term.t) =
  match t.it with
  | Term.Lam (x, _, ty, b) -> (Func.show x, ty) :: binders b
  | Term.App (hd, args) -> List.concat_map binders (hd :: args)
  | Term.Cast (u, _) | Term.Parens u -> binders u
  | _ -> []

let binders_data bs =
  let one (x, ty) =
    let ty = match ty with None -> "none" | Some ty -> "(some " ^ Print.type_data ty ^ ")" in
    "(reflect.binder " ^ Print.string_literal x ^ " " ^ ty ^ ")"
  in
  "(reflect.binders [" ^ String.concat ", " (List.map one bs) ^ "])"

(* The macros used by a term (rules that use one are not reflected) *)
let rec macros (t : Term.t) =
  match t.it with
  | Term.Const c when Scope.is_macro (Func.show c) -> [ Func.show c ]
  | Term.App (hd, args) -> List.concat_map macros (hd :: args)
  | Term.Lam (_, _, _, b) -> macros b
  | Term.Cast (u, _) | Term.Parens u -> macros u
  | _ -> []

let rule_of_clause (c : (Term.t, raw_attribute list, unit, unit) Clause.t) : rule option =
  let head, body = split_rule c.body in
  match head_symbol head, macros c.body with
  | None, _ -> warn c.loc "a rule whose head is not a predicate is not reflected"; None
  | Some _, m :: _ -> warn c.loc "a rule using the macro %s is not reflected" m; None
  | Some pred, [] ->
      let head, body = Spill.rule head body in
      if Spill.unhandled head || Spill.unhandled body then
        warn c.loc "a spill under a lambda or in a hypothesis is left as written";
      Some { pred; loc = c.loc; attrs = c.attributes; head = data_of_pattern head; body }

(* ------------------------------------------------------------------------ *)
(* The order of the rules: :before, :after, :replace, :remove *)

let place_rules (rules : rule list) : rule list =
  let named n r = name_of r.attrs = Some n in
  let add placed (r : rule) =
    let insert_at ~before n =
      if not (List.exists (named n) placed) then begin
        warn r.loc "no rule is named %S: the rule is added at the end" n;
        placed @ [ r ]
      end else
        List.concat_map (fun x -> if named n x then (if before then [ r; x ] else [ x; r ]) else [ x ]) placed
    in
    match
      List.find_map
        (function
          | Before n -> Some (`Before n) | After n -> Some (`After n)
          | Replace n -> Some (`Replace n) | Remove n -> Some (`Remove n) | _ -> None)
        r.attrs
    with
    | Some (`Before n) -> insert_at ~before:true n
    | Some (`After n) -> insert_at ~before:false n
    | Some (`Replace n) -> List.map (fun x -> if named n x then r else x) placed
    | Some (`Remove n) -> List.filter (fun x -> not (named n x)) placed
    | None -> placed @ [ r ]
  in
  List.fold_left add [] rules

(* ------------------------------------------------------------------------ *)
(* Facts *)

(* ------------------------------------------------------------------------ *)
(* Facts *)

(* The type variables Ty_X that occur once in a fact are renamed _Ty_X, as
   the type checker asks for linear variables. *)
let discard_linear_type_variables text =
  let is_ident_char c =
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c = '_' || c = '\''
  in
  let n = String.length text in
  (* the occurrences of Ty_X: (start, name) *)
  let rec scan i acc =
    if i + 3 > n then List.rev acc
    else if String.sub text i 3 = "Ty_" && (i = 0 || not (is_ident_char text.[i - 1])) then begin
      let j = ref (i + 3) in
      while !j < n && is_ident_char text.[!j] do incr j done;
      scan !j ((i, String.sub text i (!j - i)) :: acc)
    end else scan (i + 1) acc
  in
  let occurrences = scan 0 [] in
  let count name = List.length (List.filter (fun (_, x) -> x = name) occurrences) in
  let b = Buffer.create (n + 8) in
  let last = List.fold_left (fun pos (start, name) ->
    Buffer.add_string b (String.sub text pos (start - pos));
    if count name = 1 then Buffer.add_char b '_';
    start) 0 occurrences in
  Buffer.add_string b (String.sub text last (n - last));
  Buffer.contents b

(* A fact is printed :untyped when the type checker cannot check it: the
   fact of an :untyped rule, or of a rule of an overloaded predicate (the
   predicate on its own has several types). *)
let fact ?(untyped = false) name args =
  (if untyped then ":untyped\n" else "")
  ^ discard_linear_type_variables ("reflect." ^ name ^ " " ^ String.concat " " args) ^ ".\n"

let rule_fact ~overloaded index (r : rule) =
  let attrs = List.filter_map attribute_data r.attrs @ [ binders_data (binders r.head @ binders r.body) ] in
  fact ~untyped:(List.mem Untyped r.attrs || StrSet.mem r.pred overloaded) "clause"
    [ Print.constant r.pred; string_of_int index; srcloc r.loc;
      "[" ^ String.concat ", " attrs ^ "]"; Print.term r.head; Print.term r.body ]

(* The arity of a kind: the number of arrows of type -> .. -> type *)
let rec arity (t : _ TypeExpression.t) =
  match t.tit with TypeExpression.TArr (_, b) -> 1 + arity b | _ -> 0

(* An old style predicate declaration: type p A -> B -> prop *)
let rec old_style_signature (t : _ TypeExpression.t) =
  match t.tit with
  | TypeExpression.TConst c when Func.show c = "prop" -> Some []
  | TypeExpression.TArr (a, b) ->
      Option.map (fun args -> (Elpi_util.Util.Mode.Output, a) :: args) (old_style_signature b)
  | _ -> None

let signature_fact ~constant name ~functional args variadic loc =
  fact "signature"
    [ Print.string_literal name; constant;
      (if functional then "reflect.functional" else "reflect.relational");
      "[" ^ String.concat ", " (List.map Print.arg_data args) ^ "]";
      (if variadic then "tt" else "ff"); srcloc loc ]

let rec has_type_variables (t : _ TypeExpression.t) =
  let open TypeExpression in
  match t.tit with
  | TConst c -> Func.is_uvar_name c
  | TApp (_, a, args) -> List.exists has_type_variables (a :: args)
  | TArr (a, b) -> has_type_variables a || has_type_variables b
  | TPred (_, args, _) -> List.exists (fun (_, t) -> has_type_variables t) args

(* An overloaded constant is cast to its declared type when the type is
   monomorphic; a cast cannot mention type variables, so the constant of an
   overloaded polymorphic symbol is left out (a fresh variable _). *)
let symbol_fact ~overloaded (t : _ Type.t) =
  let name = Func.show t.name in
  let is_overloaded = StrSet.mem name overloaded in
  let constant =
    if is_overloaded && has_type_variables t.ty then "_"
    else if is_overloaded then "(" ^ Print.constant name ^ " : " ^ Print.type_expr t.ty ^ ")"
    else Print.constant name
  in
  match t.ty.tit with
  | TypeExpression.TPred (attrs, args, variadic) ->
      signature_fact ~constant name ~functional:(Print.is_functional (attrs @ t.attributes)) args variadic t.loc
  | _ ->
      match old_style_signature t.ty with
      | Some args -> signature_fact ~constant name ~functional:false args false t.loc
      | None ->
          fact "constructor"
            [ Print.string_literal name; constant; Print.type_data t.ty; srcloc t.loc ]

let type_abbrev_fact (ta : (Func.t, _ TypeExpression.t) TypeAbbreviation.t) =
  let rec params = function
    | TypeAbbreviation.Lam (x, _, v) -> let ps, body = params v in (Func.show x :: ps, body)
    | TypeAbbreviation.Ty t -> ([], t)
  in
  let ps, body = params ta.value in
  let lhs =
    "(reflect.tcon " ^ Print.string_literal (Func.show ta.name) ^ " ["
    ^ String.concat ", " (List.map Print.type_variable ps) ^ "])"
  in
  fact "type-abbrev" [ lhs; Print.type_data body; srcloc ta.loc ]

let sequent_data ~pattern (q : Term.t Chr.sequent) =
  let part t = Print.term (if pattern then data_of_pattern t else t) in
  "(reflect.sequent " ^ part q.eigen ^ " " ^ part q.context ^ " " ^ part q.conclusion ^ ")"

let chr_fact index clique (r : (raw_attribute list, Term.t) Chr.t) =
  let list l = "[" ^ String.concat ", " l ^ "]" in
  let option f = function None -> "none" | Some x -> "(some " ^ f x ^ ")" in
  fact "chr-rule"
    [ string_of_int index; srcloc r.loc; list (List.filter_map attribute_data r.attributes);
      list (List.map Print.constant clique);
      list (List.map (sequent_data ~pattern:true) r.to_match);
      list (List.map (sequent_data ~pattern:true) r.to_remove);
      option Print.term r.guard; option (sequent_data ~pattern:false) r.new_goal ]

(* ------------------------------------------------------------------------ *)
(* The whole program *)

let header =
  "% Generated by elpi-reflect: the program as data (see elpi-tools/reflect/README.md).\n"

(* The symbols declared more than once (overloaded) *)
let overloaded_symbols (decls : Scope.resolved list) =
  let names = List.concat_map (fun (d : Scope.resolved) -> match d.decl with
    | Program.Type ts -> List.map (fun (t : _ Type.t) -> Func.show t.name) ts
    | Program.Pred t -> [ Func.show t.name ]
    | _ -> []) decls in
  let sorted = List.sort compare names in
  let rec dups = function
    | a :: (b :: _ as rest) when a = b -> a :: dups rest
    | _ :: rest -> dups rest
    | [] -> []
  in
  StrSet.of_list (dups sorted)

(* [facts ~defines ~rules decls]: the text of the facts for the resolved
   declarations [decls]; the rules and CHR rules only when [rules]. *)
let facts ~defines ~rules (decls : Scope.resolved list) : string =
  let overloaded = overloaded_symbols decls in
  let b = Buffer.create 4096 in
  let section title = Buffer.add_string b ("\n% -- " ^ title ^ "\n") in
  let each f = List.iter (fun (d : Scope.resolved) -> f d) decls in
  section "data types";
  each (fun d -> match d.decl with
    | Program.Kind ks ->
        List.iter (fun (k : _ Type.t) ->
          Buffer.add_string b (fact "data-type" [ Print.string_literal (Func.show k.name);
                                                  string_of_int (arity k.ty); srcloc k.loc ])) ks
    | _ -> ());
  section "constructors and signatures";
  each (fun d -> match d.decl with
    | Program.Type ts -> List.iter (fun t -> Buffer.add_string b (symbol_fact ~overloaded t)) ts
    | Program.Pred t -> Buffer.add_string b (symbol_fact ~overloaded t)
    | _ -> ());
  section "type abbreviations";
  each (fun d -> match d.decl with
    | Program.TypeAbbreviation ta -> Buffer.add_string b (type_abbrev_fact ta)
    | _ -> ());
  if rules then begin
    section "rules";
    let rules =
      List.filter_map (fun (d : Scope.resolved) -> match d.decl with
        | Program.Clause c when enabled defines c.attributes -> rule_of_clause c
        | _ -> None) decls
    in
    let counts = Hashtbl.create 16 in
    List.iter (fun r ->
      let n = 1 + Option.value ~default:0 (Hashtbl.find_opt counts r.pred) in
      Hashtbl.replace counts r.pred n;
      Buffer.add_string b (rule_fact ~overloaded n r)) (place_rules rules);
    section "CHR rules";
    let index = ref 0 in
    each (fun d -> match d.decl with
      | Program.Chr r when enabled defines r.attributes ->
          incr index;
          Buffer.add_string b (chr_fact !index d.clique r)
      | _ -> ())
  end;
  Buffer.contents b

(* ------------------------------------------------------------------------ *)
(* Parsing *)

exception Error of string

module Parser (C : sig val paths : string list end) = Elpi_parser.Parse.Make (struct
  let versions = Elpi_util.Util.StrMap.empty
  let resolver = Elpi.API.Parse.std_resolver ~paths:C.paths ()
end)

let check_errors = function
  | p, [], _ -> p
  | _, errors, _ ->
      let show (e : Elpi_util.Util.error) =
        (match e.loc with Some l -> Loc.show l ^ ": " | None -> "") ^ e.message
      in
      raise (Error (String.concat "\n" (List.map show errors)))

(* [parse ~paths file]: the parsed file, accumulated files included *)
let parse ~paths file : Program.t =
  let module P = Parser (struct let paths = paths end) in
  try check_errors (P.program file)
  with Elpi_parser.Parse.ParseError (loc, msg) -> raise (Error (Loc.show loc ^ ": " ^ msg))

(* The declarations of Elpi's builtins and standard library, as printed by
   elpi -document-builtins *)
let builtin_declarations () : Program.t =
  let text = Format.asprintf "%a" (fun fmt () -> Elpi.API.BuiltIn.document_fmt fmt Elpi.Builtin.std_builtins) () in
  let module P = Parser (struct let paths = [] end) in
  let loc = Loc.initial "builtin.elpi" in
  try check_errors (P.program_from ~loc ~digest:(Digest.string text) (Lexing.from_string text))
  with Elpi_parser.Parse.ParseError (loc, msg) -> raise (Error (Loc.show loc ^ ": " ^ msg))

(* The connectives of rules and goals are syntax, not constants that a fact
   can mention: their declarations are not reflected. *)
let connectives = StrSet.of_list [ ":-"; ","; "=>"; "==>"; "uvar"; "as"; ";"; "pi"; "sigma" ]

let not_a_connective (d : Scope.resolved) =
  match d.decl with
  | Program.Type ts -> List.for_all (fun (t : _ Type.t) -> not (StrSet.mem (Func.show t.name) connectives)) ts
  | Program.Pred t -> not (StrSet.mem (Func.show t.name) connectives)
  | _ -> true

let in_block file (p : Program.t) =
  let loc = Loc.initial file in
  { p with ast = (Program.Begin loc :: p.ast) @ [ Program.End loc ] }

(* [reflect_files ~paths ~defines ~builtins files]: the facts of the program
   made of [files] (each as if accumulated); with [builtins], also the
   declarations (not the rules) of Elpi's builtins and standard library. *)
let reflect_files ?(paths = []) ?(defines = []) ?(builtins = false) files : string =
  let defines = StrSet.of_list defines in
  let program = List.concat_map (fun file -> Scope.resolve_program (in_block file (parse ~paths file))) files in
  let builtin_text =
    if not builtins then ""
    else
      "\n% == Elpi builtins and standard library (declarations only)\n"
      ^ facts ~defines ~rules:false
          (List.filter not_a_connective (Scope.resolve_program (in_block "builtin.elpi" (builtin_declarations ()))))
  in
  header ^ facts ~defines ~rules:true program ^ builtin_text
