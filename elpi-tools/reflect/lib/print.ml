(* Printing parsed Elpi terms and types back as Elpi source.

   Every compound term is printed between parentheses, so that the output
   does not depend on the precedence of the operators; lists are printed
   with the [a, b | T] syntax. *)

open Elpi_parser.Ast

let buffer_add = Buffer.add_string

(* ------------------------------------------------------------------------ *)
(* Literals *)

(* Elpi string literals (lexer.mll.in, rule string) *)
let string_literal s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter
    (function
      | '"' -> buffer_add b "\\\""
      | '\\' -> buffer_add b "\\\\"
      | '\n' -> buffer_add b "\\n"
      | '\t' -> buffer_add b "\\t"
      | '\r' -> buffer_add b "\\r"
      | c -> Buffer.add_char b c)
    s;
  Buffer.add_char b '"';
  Buffer.contents b

let float_literal f =
  let s = Printf.sprintf "%.17g" f in
  if String.exists (fun c -> c = '.' || c = 'e' || c = 'n' || c = 'i') s then s else s ^ ".0"

let cdata_literal (c : Elpi_util.Util.CData.t) =
  if cint.isc c then
    let n = cint.cout c in
    if n < 0 then Printf.sprintf "(%d)" n else string_of_int n
  else if cstring.isc c then string_literal (cstring.cout c)
  else if cfloat.isc c then
    let f = cfloat.cout c in
    if f < 0. then "(" ^ float_literal f ^ ")" else float_literal f
  else Elpi_util.Util.CData.show c

(* ------------------------------------------------------------------------ *)
(* Operators *)

(* The infix operators spelled with letters (the others are made of
   symbols, see parser/lexer_config.ml) *)
let word_infixes =
  [ "is"; "div"; "mod"; "as"; "r+"; "i+"; "s+"; "r-"; "i-"; "s-"; "r*"; "i*"; "s*";
    "r<"; "i<"; "s<"; "r=<"; "i=<"; "s=<"; "r>"; "i>"; "s>"; "r>="; "i>="; "s>=" ]

let word_prefixes = [ "r~"; "i~" ]
let symbol_chars = ":?;=<>^+-*/|&#,`'~\\"

let is_symbolic name =
  String.length name > 0 && String.contains symbol_chars name.[0]

let is_infix name = (is_symbolic name && name.[0] <> '~') || List.mem name word_infixes
let is_prefix name = (String.length name > 0 && name.[0] = '~') || List.mem name word_prefixes

(* A constant on its own: an operator is put between parentheses *)
(* pi and sigma are keywords: on their own they need parentheses too *)
let binder_keywords = [ "pi"; "sigma" ]

let constant name =
  if name = "%dummy" then "_"
  else if is_infix name || is_prefix name || List.mem name binder_keywords then "(" ^ name ^ ")"
  else name

(* ------------------------------------------------------------------------ *)
(* Types, in Elpi syntax *)

let mode_prefix = function Elpi_util.Util.Mode.Input -> "i:" | Elpi_util.Util.Mode.Output -> "o:"

let is_functional attrs = List.exists (function Functional -> true | _ -> false) attrs

let rec type_expr (t : _ TypeExpression.t) =
  let open TypeExpression in
  match t.tit with
  | TConst c -> Func.show c
  | TApp (c, a, args) -> "(" ^ String.concat " " (Func.show c :: List.map type_expr (a :: args)) ^ ")"
  | TArr (a, b) -> "(" ^ type_expr a ^ " -> " ^ type_expr b ^ ")"
  | TPred (attrs, args, variadic) ->
      let dots = if variadic then " .." else "" in
      let open Elpi_util.Util.Mode in
      let inputs = List.filter (fun (m, _) -> m = Input) args in
      let outputs = List.filter (fun (m, _) -> m = Output) args in
      let inputs_first = args = inputs @ outputs in
      let types l = String.concat ", " (List.map (fun (_, t) -> type_expr t) l) in
      if is_functional attrs && inputs_first then
        (* (func I1, I2 -> O1) *)
        let arrow = if outputs = [] then "" else " -> " ^ types outputs in
        if args = [] then "(func)" else "(func " ^ types inputs ^ arrow ^ dots ^ ")"
      else
        (* (pred i:I1, o:O1): the order of the modes is free *)
        let args = List.map (fun (m, t) -> mode_prefix m ^ type_expr t) args in
        if args = [] then "(pred)" else "(pred " ^ String.concat ", " args ^ dots ^ ")"

(* ------------------------------------------------------------------------ *)
(* Types, as reflect.ty data *)

(* Type parameters become the Elpi variables Ty_A, Ty_B ... *)
let type_variable name = "Ty_" ^ name

let rec type_data (t : _ TypeExpression.t) =
  let open TypeExpression in
  let tcon name args = "(reflect.tcon " ^ string_literal name ^ " [" ^ String.concat ", " args ^ "])" in
  match t.tit with
  | TConst c when Func.is_uvar_name c -> type_variable (Func.show c)
  | TConst c when Func.show c = "any" -> "reflect.tany"
  | TConst c when Func.show c = "prop" -> "(reflect.tpred reflect.relational [])"
  | TConst c -> tcon (Func.show c) []
  | TApp (c, a, args) -> tcon (Func.show c) (List.map type_data (a :: args))
  | TArr (a, b) -> "(reflect.tarrow " ^ type_data a ^ " " ^ type_data b ^ ")"
  | TPred (attrs, args, _) ->
      "(reflect.tpred " ^ functionality attrs ^ " [" ^ String.concat ", " (List.map arg_data args) ^ "])"

and functionality attrs = if is_functional attrs then "reflect.functional" else "reflect.relational"

and arg_data (m, t) =
  let mode = match m with Elpi_util.Util.Mode.Input -> "reflect.in" | Elpi_util.Util.Mode.Output -> "reflect.out" in
  "(reflect.arg " ^ mode ^ " " ^ type_data t ^ ")"

(* ------------------------------------------------------------------------ *)
(* Terms *)

let rec list_elements (t : Term.t) : Term.t list * Term.t option =
  match t.it with
  | Term.App ({ it = Term.Const c; _ }, [ h; tl ]) when Func.equal c Func.consf ->
      let elems, tail = list_elements tl in
      (h :: elems, tail)
  | Term.Const c when Func.equal c Func.nilf -> ([], None)
  | Term.Parens u -> list_elements u
  | _ -> ([], Some t)

let rec term (t : Term.t) : string =
  match t.it with
  | Term.Const c -> constant (Func.show c)
  | Term.CData c -> cdata_literal c
  | Term.Quoted q -> "{{" ^ q.data ^ "}}"
  | Term.Parens u -> term u
  | Term.Cast (u, ty) -> "(" ^ term u ^ " : " ^ type_expr ty ^ ")"
  | Term.Lam (x, _, ty, body) -> "(" ^ binder x ty ^ " " ^ term body ^ ")"
  | Term.App ({ it = Term.Const c; _ }, [ g ]) when Func.equal c Func.spillf -> "{" ^ term g ^ "}"
  | Term.App ({ it = Term.Const c; _ }, [ _; _ ]) when Func.equal c Func.consf ->
      let elems, tail = list_elements t in
      let elems = String.concat ", " (List.map term elems) in
      (match tail with None -> "[" ^ elems ^ "]" | Some tl -> "[" ^ elems ^ " | " ^ term tl ^ "]")
  | Term.App ({ it = Term.Const c; _ }, [ { it = Term.Lam (x, _, ty, body); _ } ])
    when Func.equal c Func.pif || Func.equal c Func.sigmaf ->
      "(" ^ Func.show c ^ " " ^ binder x ty ^ " " ^ term body ^ ")"
  | Term.App ({ it = Term.Const c; _ }, args) when Func.equal c Func.andf ->
      "(" ^ String.concat ", " (List.map term args) ^ ")"
  | Term.App ({ it = Term.Const c; _ }, [ a; b ]) when is_infix (Func.show c) ->
      "(" ^ term a ^ " " ^ Func.show c ^ " " ^ term b ^ ")"
  | Term.App ({ it = Term.Const c; _ }, [ a ]) when is_prefix (Func.show c) ->
      "(" ^ Func.show c ^ " " ^ term a ^ ")"
  | Term.App (hd, args) -> "(" ^ String.concat " " (List.map term (hd :: args)) ^ ")"

and binder x ty =
  match ty with
  | None -> Func.show x ^ "\\"
  | Some ty -> Func.show x ^ " : " ^ type_expr ty ^ " \\"
