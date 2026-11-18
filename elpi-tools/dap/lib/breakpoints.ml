(* Source breakpoints: from a line of a file to the clause it belongs to.

   elpi-debug numbers the rules of the program and gives the line where
   each starts, and the lines where the declarations start (types,
   constructors, signatures, CHR rules).  A line belongs to the last item
   of its file starting at or before it; a breakpoint is set when that
   item is a rule, on that rule, and shown at its first line.  (So the
   comment lines just after a rule count as part of it; a line before the
   first item, or in a declaration, has no breakpoint.) *)

open Debuggee

(* [canonical path]: the absolute path with symbolic links resolved (the
   path itself if it does not exist). *)
let canonical path = try Unix.realpath path with Unix.Unix_error _ -> path

(* [with_canonical_files program]: the listing with canonical paths, to
   compare them with the paths of the client. *)
let with_canonical_files program =
  let canonical_location (l : location) = { l with file = canonical l.file } in
  {
    rules = List.map (fun r -> { r with at = canonical_location r.at }) program.rules;
    declarations = List.map canonical_location program.declarations;
  }

(* An item of a file: a rule, or a declaration (no rule). *)
type item = { starts : int; rule : rule option }

(* [items_of program file]: the items of the file, by their first line. *)
let items_of program file =
  let rules = List.filter_map (fun r -> if r.at.file = file then Some { starts = r.at.line; rule = Some r } else None) program.rules in
  let declarations =
    List.filter_map (fun (d : location) -> if d.file = file then Some { starts = d.line; rule = None } else None) program.declarations
  in
  List.stable_sort (fun a b -> compare a.starts b.starts) (rules @ declarations)

(* [rule_at program ~file ~line]: the rule that holds the line, if any;
   file is a canonical path. *)
let rule_at program ~file ~line =
  let before = List.filter (fun item -> item.starts <= line) (items_of program file) in
  match List.rev before with
  | [] -> None
  | last :: _ ->
      (* the items starting on the line of the last one: a rule among them wins *)
      let same_line = List.filter (fun item -> item.starts = last.starts) before in
      List.find_map (fun item -> item.rule) same_line

(* [has_rules program predicate]: the program has rules for the predicate. *)
let has_rules program predicate = List.exists (fun r -> r.predicate = predicate) program.rules

(* [changes ~before ~after]: the commands that turn the set of breakpoints
   [before] into [after] (lists without duplicates), as pairs (sign, x):
   removals first. *)
let changes ~before ~after =
  let removed = List.filter (fun x -> not (List.mem x after)) before in
  let added = List.filter (fun x -> not (List.mem x before)) after in
  List.map (fun x -> ("-", x)) removed @ List.map (fun x -> ("+", x)) added
