(* cyp: colour a proof written in Markdown by checking each of its steps
   with Rocq.

   cyp proof.md  writes  proof.cyp.v    (one goal per step)
                         proof.checked.md (the proof, each step marked)

   The format is described in README.md. *)

(* ------------------------------------------------------------------ *)
(* Small helpers                                                       *)

let read_file f =
  let ic = open_in_bin f in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic; s

let write_file f s =
  let oc = open_out_bin f in
  output_string oc s; close_out oc

let lines s = String.split_on_char '\n' s

let starts_with p s =
  String.length s >= String.length p && String.sub s 0 (String.length p) = p

let trim = String.trim

let indent_of s =
  let n = String.length s in
  let rec go i = if i < n && s.[i] = ' ' then go (i + 1) else i in
  go 0

let contains s sub =
  try ignore (Str.search_forward (Str.regexp_string sub) s 0); true
  with Not_found -> false

(* ------------------------------------------------------------------ *)
(* The document                                                        *)

(* The role of a formula, given by the words written before it. *)
type role = Var | Hyp | Claim | Fact

(* A piece of text: plain words, a formula with its role, or the
   justification [*by tac*]. *)
type piece = Text of string | Formula of role * string | By of string

type step = {
  id : int;
  pieces : piece list;
  children : step list;
  first : int;                    (* its lines in the source, from 0 *)
  last : int;
}

type prop = {
  name : string;
  pid : int;                      (* the id of the statement *)
  statement : piece list;
  steps : step list;
  sfirst : int;                   (* the lines of the statement *)
  slast : int;
}

type header = {
  require : string;               (* the Rocq preamble *)
  default_by : string;            (* the default justification *)
  timeout : int;                  (* seconds per step *)
  flags : string;                 (* options of rocq c, e.g. load paths *)
}

(* Words that give the role of the formulas that follow them. *)
(* The words of each language: [en], [fr] and [it], chosen by the field
   [lang:] of the header. *)
let role_words_of = function
  | "fr" -> [
      "soit", Var; "soient", Var; "considérons", Var;
      "si", Hyp; "supposons", Hyp; "posons par hypothèse", Hyp;
      "à partir de", Fact; "en utilisant", Fact; "puisque", Fact;
      "d'après", Fact; "grâce à", Fact;
      "alors", Claim; "montrons", Claim; "prouvons", Claim;
      "nous avons", Claim; "on a", Claim; "donc", Claim; "ainsi", Claim;
      "d'où", Claim; "nous en déduisons", Claim; "nous déduisons", Claim;
      "nous obtenons", Claim; "on obtient", Claim; "c'est-à-dire", Claim;
      "équivalent à", Claim;
    ]
  | "it" -> [
      "sia", Var; "siano", Var; "consideriamo", Var;
      "se", Hyp; "supponiamo", Hyp; "assumiamo", Hyp;
      "da", Fact; "usando", Fact; "poiché", Fact; "grazie a", Fact;
      "allora", Claim; "mostriamo", Claim; "dimostriamo", Claim;
      "abbiamo", Claim; "quindi", Claim; "dunque", Claim; "ne segue", Claim;
      "ne deduciamo", Claim; "otteniamo", Claim; "cioè", Claim;
    ]
  | _ -> [
      "let", Var;
      "if", Hyp; "assume", Hyp; "suppose", Hyp; "where", Hyp;
      "from", Fact; "using", Fact; "since", Fact; "because", Fact;
      "then", Claim; "show", Claim; "prove", Claim; "have", Claim;
      "get", Claim; "thus", Claim; "hence", Claim; "so", Claim;
      "written as", Claim; "is", Claim; "obtain", Claim; "deduce", Claim;
    ]

(* Words that make a step go backwards: its formula replaces the goal. *)
let backward_words_of = function
  | "fr" -> [ "il suffit"; "équivaut à montrer"; "revient à"; "se réduit à" ]
  | "it" -> [ "basta"; "è sufficiente"; "equivale a dimostrare"; "si riduce a" ]
  | _ -> [ "suffices"; "enough"; "equivalent to prove"; "written as";
           "amounts to"; "reduces to" ]

(* The language of the proof being read. *)
let lang = ref "en"

(* Lower case, also for the accented capitals of French and Italian. *)
let lower s =
  List.fold_left (fun s (a, b) -> Str.global_replace (Str.regexp_string a) b s)
    (String.lowercase_ascii s)
    [ "À", "à"; "Â", "â"; "Ç", "ç"; "É", "é"; "È", "è"; "Ê", "ê"; "Ë", "ë";
      "Î", "î"; "Ï", "ï"; "Ô", "ô"; "Ù", "ù"; "Û", "û"; "Ì", "ì"; "Ò", "ò" ]

(* The role given by the last role word of [txt], if any. *)
let role_of_text txt =
  let t = " " ^ lower txt ^ " " in
  let best = ref None in
  List.iter (fun (w, r) ->
      let re = Str.regexp ("[^a-z]" ^ Str.quote w ^ "[^a-z]") in
      let rec last pos acc =
        match Str.search_forward re t pos with
        | p -> last (p + 1) (Some p)
        | exception Not_found -> acc in
      match last 0 None with
      | Some p ->
          (match !best with
           | Some (q, _) when q >= p -> ()
           | _ -> best := Some (p, r))
      | None -> ()) (role_words_of !lang);
  Option.map snd !best

(* An explicit role, written right after a formula: `x`{.hyp}. *)
let tag_re = Str.regexp "{\\.\\(var\\|hyp\\|claim\\|fact\\)}"

(* Does a formula state something: an equality, a comparison, a
   connective or a quantifier? *)
let relation_re =
  Str.regexp ".*\\(=\\|<\\|>\\|->\\|/\\\\\\|\\\\/\\|~\\|forall\\|exists\\|_format\\|True\\|False\\)"
let is_relation f = Str.string_match relation_re f 0

(* Cut a text into pieces: `...` are formulas, *by ...* a justification. *)
let pieces_of_text ~default txt =
  let by_re = Str.regexp "\\*by \\([^*]*\\)\\*" in
  let txt, by =
    match Str.search_forward by_re txt 0 with
    | p ->
        let tac = Str.matched_group 1 txt in
        let e = Str.match_end () in
        let tac = Str.global_replace (Str.regexp_string "`") "" tac in
        (String.sub txt 0 p ^ String.sub txt e (String.length txt - e),
         Some (trim tac))
    | exception Not_found -> (txt, None) in
  let parts = String.split_on_char '`' txt in
  let role = ref default in
  let rec go i = function
    | [] -> []
    | s :: rest when i mod 2 = 0 ->
        (match role_of_text s with Some r -> role := r | None -> ());
        (if s = "" then [] else [Text s]) @ go (i + 1) rest
    | s :: next :: rest when Str.string_match tag_re next 0 ->
        (* an explicit role written right after the formula *)
        let r = match Str.matched_group 1 next with
          | "var" -> Var | "hyp" -> Hyp | "fact" -> Fact | _ -> Claim in
        let e = Str.match_end () in
        let f = Formula (r, s) in
        f :: go (i + 1) (String.sub next e (String.length next - e) :: rest)
    | s :: rest ->
        (* a formula with no relation is a mention (a number, a function),
           not a claim *)
        let r = if !role = Claim && not (is_relation s) then Fact else !role in
        let f = Formula (r, s) in f :: go (i + 1) rest in
  let ps = go 0 parts in
  match by with Some t -> ps @ [By t] | None -> ps

let counter = ref 0
let fresh () = incr counter; !counter

(* A list item starts with "- ", "* " or "1. ". *)
let item_re = Str.regexp "^\\(-\\|\\*\\|[0-9]+\\.\\) +"

(* Parse the list items of a proof: each item is (indent, text, first
   line, last line). *)
let rec build_steps items =
  match items with
  | [] -> []
  | (ind, txt, first, last) :: rest ->
      let rec split acc = function
        | ((i, _, _, _) as it) :: r when i > ind -> split (it :: acc) r
        | r -> (List.rev acc, r) in
      let sub, rest = split [] rest in
      let id = fresh () in
      { id; pieces = pieces_of_text ~default:Claim txt;
        children = build_steps sub; first; last } :: build_steps rest

(* The rule database and its tactic (rules/cyp_rules.v), put in front of
   the rule file of a proof. *)
let rules_prelude = Prelude.text

let absolute d = if Filename.is_relative d then Filename.concat (Sys.getcwd ()) d else d

let parse ~dir src =
  (* a path of the header, relative to the directory of the proof *)
  let abs f = if Filename.is_relative f then Filename.concat (absolute dir) f else f in
  (* the directories of -Q and -R in flags, relative to that directory *)
  let relative_flags fl =
    let rec go = function
      | ("-Q" | "-R" | "-I" as o) :: d :: r -> o :: abs d :: go r
      | x :: r -> x :: go r
      | [] -> [] in
    String.concat " " (go (List.filter (( <> ) "") (String.split_on_char ' ' fl))) in
  let ls = lines src in
  (* the front matter between two lines "---" *)
  let header, body =
    match ls with
    | l :: rest when trim l = "---" ->
        let rec take acc = function
          | l :: r when trim l = "---" -> (List.rev acc, r)
          | l :: r -> take (l :: acc) r
          | [] -> (List.rev acc, []) in
        take [] rest
    | _ -> ([], ls) in
  (* the number of the first line of [body] *)
  let offset = if header = [] && body == ls then 0 else List.length header + 2 in
  let get k d =
    match List.find_opt (fun l -> starts_with (k ^ ":") (trim l)) header with
    | Some l ->
        let l = trim l in
        trim (String.sub l (String.length k + 1)
                (String.length l - String.length k - 1))
    | None -> d in
  let h = {
    require = get "require" "From Stdlib Require Import ZArith Lia.";
    default_by = get "by" "lia";
    timeout = int_of_string (get "timeout" "10");
    flags = relative_flags (get "flags" "");
  } in
  lang := get "lang" "en";
  let h =
    let scope = get "scope" "" in
    if scope = "" then h
    else { h with require = h.require ^ "\nOpen Scope " ^ scope ^ "." } in
  (* a rule file: Rocq text (Ltac definitions, Elpi Accumulate cyp.db) put
     after the preamble; the default justification then tries the rules
     first *)
  let h =
    (* several rule files, in order, copied after the preamble (copied,
       not loaded: a lemma proved by [interval] in a loaded file would
       keep its numerical check as an assumption) *)
    match List.filter (( <> ) "") (String.split_on_char ' ' (get "rules" "")) with
    | [] -> h
    | fs ->
        let text = String.concat "\n" (List.map (fun f -> read_file (abs f)) fs) in
        { h with require = h.require ^ "\n" ^ rules_prelude ^ "\n" ^ text;
                 default_by = "elpi cyp_by | " ^ h.default_by } in
  (* the propositions, each starting with a line "# name" *)
  let props = ref [] in
  let cur = ref None in
  let flush () =
    match !cur with
    | Some (name, stmt, items) ->
        let pid = fresh () in
        let stmt_text = String.concat " " (List.rev_map snd stmt) in
        let sfirst, slast =
          match stmt with
          | [] -> (0, 0)
          | (l, _) :: _ -> (fst (List.nth stmt (List.length stmt - 1)), l) in
        let items = List.rev items in
        props := { name; pid;
                   statement = pieces_of_text ~default:Claim stmt_text;
                   steps = build_steps items; sfirst; slast } :: !props
    | None -> () in
  List.iteri (fun k l ->
      let k = k + offset in
      let t = trim l in
      if starts_with "# " t then begin
        flush ();
        cur := Some (trim (String.sub t 2 (String.length t - 2)), [], [])
      end else
        match !cur with
        | None -> ()
        | Some (n, stmt, items) ->
            let ind = indent_of l in
            if Str.string_match item_re t 0 then
              let txt = String.sub t (Str.match_end ())
                  (String.length t - Str.match_end ()) in
              cur := Some (n, stmt, (ind, txt, k, k) :: items)
            else if t = "" then ()
            else (match items with
                | (i, txt, f, _) :: r when ind > 0 ->
                    cur := Some (n, stmt, (i, txt ^ " " ^ t, f, k) :: r)
                | _ when items = [] -> cur := Some (n, (k, t) :: stmt, items)
                | _ -> ())) body;
  flush ();
  (h, List.rev !props)

(* ------------------------------------------------------------------ *)
(* The obligations                                                     *)

(* One goal to check: under [vars] and [hyps], [concl] holds by [tac].
   It belongs to the step (or statement) [owner]. *)
type obligation = {
  num : int;
  owner : int;
  vars : string list;
  hyps : string list;
  concl : string;
  tac : string;
}

let formulas r ps =
  List.filter_map (function Formula (r', f) when r' = r -> Some f | _ -> None)
    ps

let conj = function
  | [] -> None
  | fs -> Some (String.concat " /\\ " (List.map (fun f -> "(" ^ f ^ ")") fs))

let by_of h ps =
  match List.find_map (function By t -> Some t | _ -> None) ps with
  | Some t -> t
  | None -> "first [" ^ h.default_by ^ "]"

(* A step goes backwards when the last phrase before its first claim (a
   role word or a backward phrase) is a backward phrase: in "it is enough
   to check all cases, so `C`", the claim is announced by "so". *)
let is_backward ps =
  let last_pos re t =
    let rec go pos acc =
      match Str.search_forward re t pos with
      | p -> go (p + 1) (Some p)
      | exception Not_found -> acc in
    go 0 None in
  let phrase t =
    let t = " " ^ lower t ^ " " in
    let best words kind acc =
      List.fold_left (fun acc w ->
          let re = Str.regexp ("[^a-zà-ÿ]" ^ Str.quote w ^ "[^a-zà-ÿ]") in
          match last_pos re t, acc with
          | Some p, Some (q, _) when q >= p -> acc
          | Some p, _ -> Some (p, kind)
          | None, _ -> acc) acc words in
    let acc = best (List.map fst (role_words_of !lang)) false None in
    Option.map snd (best (backward_words_of !lang) true acc) in
  let rec go last = function
    | Text t :: r -> go (match phrase t with Some k -> k | None -> last) r
    | Formula (Claim, _) :: _ -> last
    | _ :: r -> go last r
    | [] -> false in
  go false ps

(* [forall vars, hyps -> c], the result of a local scope *)
(* A variable "u := e" is a local definition: [let u := e in]. *)
let generalise vars hyps c =
  let body = String.concat " -> " (List.map (fun f -> "(" ^ f ^ ")") (hyps @ [c])) in
  List.fold_right (fun v acc ->
      if contains v ":=" then "let " ^ v ^ " in " ^ acc
      else "forall (" ^ v ^ "), " ^ acc) vars body

let obligations h props =
  let obs = ref [] in
  let n = ref 0 in
  let add owner vars hyps concl tac =
    incr n;
    obs := { num = !n; owner; vars; hyps; concl; tac } :: !obs in
  (* the steps [st], in the context [vars] [hyps]: their obligations, and
     the context and the goal after them *)
  let rec steps vars hyps goal st =
    match st with
    | [] -> (hyps, goal)
    | s :: rest ->
        let sv = formulas Var s.pieces and sh = formulas Hyp s.pieces in
        match conj (formulas Claim s.pieces) with
        | None when sv <> [] || sh <> [] ->
            (* a local scope: "Let x" or "Assume A" introduces [sv] and [sh]
               for its sub-steps, or else for the steps that follow it; its
               result is [forall sv, sh -> C], C its last claim *)
            let body, rest = if s.children <> [] then (s.children, rest) else (rest, []) in
            let inner = hyps @ sh in
            let after, _ = steps (vars @ sv) inner goal body in
            let hyps =
              if List.length after > List.length inner then
                hyps @ [generalise sv sh (List.nth after (List.length after - 1))]
              else hyps in
            steps vars hyps goal rest
        | None -> steps vars hyps goal rest        (* a comment *)
        | Some c ->
            let tac = by_of h s.pieces in
            if is_backward s.pieces then begin
              (* the new goal [c] implies the old one *)
              add s.id vars (hyps @ [c]) goal tac;
              if s.children <> [] then
                level s.id (by_of h []) vars hyps c s.children;
              steps vars hyps c rest
            end else begin
              if s.children <> [] then level s.id tac vars hyps c s.children
              else add s.id vars hyps c tac;
              steps vars (hyps @ [c]) goal rest
            end
  (* the steps [st] prove [goal]; the last obligation, that [goal]
     follows, belongs to [owner] *)
  and level owner owner_tac vars hyps goal st =
    let hyps, goal = steps vars hyps goal st in
    add owner vars hyps goal owner_tac in
  List.iter (fun p ->
      let vars = formulas Var p.statement in
      let hyps = formulas Hyp p.statement in
      match conj (formulas Claim p.statement) with
      | None -> ()
      | Some goal -> level p.pid (by_of h p.statement) vars hyps goal p.steps)
    props;
  List.rev !obs

(* Introduce exactly the context of an obligation (its variables and
   hypotheses), leaving its claim whole. *)
let intro_ctx o =
  let names v =
    match String.index_opt v ':' with
    | Some i ->
        List.length (List.filter (( <> ) "")
          (String.split_on_char ' ' (String.sub v 0 i)))
    | None -> 1 in
  let k = List.fold_left (fun n v -> n + names v) 0 o.vars + List.length o.hyps in
  if k = 0 then "idtac" else Printf.sprintf "do %d intro" k

(* The tactic of an obligation: first on the claim whole, then with the
   claim taken apart by [intros]. *)
let step_tac h o =
  Printf.sprintf "first [ solve [timeout %d (%s)] | intros; solve [timeout %d (%s)] ]"
    h.timeout o.tac h.timeout o.tac

(* The Rocq goal of an obligation. *)
let goal_of o = generalise o.vars o.hyps o.concl

(* ------------------------------------------------------------------ *)
(* Running Rocq                                                        *)

type status = Ok | Ko of string * string | Err of string

let rocq = try Sys.getenv "CYP_ROCQ" with Not_found -> "rocq c"

let tmpdir =
  let d = Filename.concat (Filename.get_temp_dir_name ())
      (Printf.sprintf "cyp-%d" (Unix.getpid ())) in
  (try Unix.mkdir d 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  d

(* Compile [src] as a file of [tmpdir]; returns the exit code and the
   output (stdout and stderr). *)
let flags = ref ""

let compile name src =
  let f = Filename.concat tmpdir (name ^ ".v") in
  let out = Filename.concat tmpdir (name ^ ".out") in
  write_file f src;
  let code = Sys.command (Printf.sprintf "cd %s && %s %s %s > %s 2>&1"
                            (Filename.quote tmpdir) rocq !flags
                            (Filename.quote (name ^ ".v")) (Filename.quote out)) in
  (code, read_file out)

let line_count s =
  List.length (lines s) - 1

(* The checking file: each obligation tells whether its tactic closes it. *)
let check_file h obs =
  let b = Buffer.create 4096 in
  Buffer.add_string b (h.require ^ "\n");
  let starts = ref [] in
  List.iter (fun o ->
      starts := (line_count (Buffer.contents b) + 1, o.num) :: !starts;
      Printf.bprintf b
        "Goal %s.\nProof. %s.\ntryif %s then idtac \"CYP-OK %d\" else idtac \"CYP-KO %d\".\nAbort.\n"
        (goal_of o) (intro_ctx o) (step_tac h o) o.num o.num) obs;
  (Buffer.contents b, List.rev !starts)

(* The obligation whose text contains line [l] of the checking file. *)
let obligation_at starts l =
  List.fold_left (fun acc (s, n) -> if s <= l then Some n else acc) None starts

let error_line out =
  let re = Str.regexp "line \\([0-9]+\\)" in
  match Str.search_forward re out 0 with
  | _ -> Some (int_of_string (Str.matched_group 1 out))
  | exception Not_found -> None

(* Check every obligation.  An obligation that Rocq rejects as a statement
   (a typo in a formula) is marked [Err] and left out, and the file is
   checked again. *)
let check h obs =
  let status = Hashtbl.create 16 in
  let seen = ref [] in
  let rec loop obs =
    let src, starts = check_file h obs in
    let code, out = compile "cyp_check" src in
    if code = 0 then
      List.iter (fun l ->
          let l = trim l in
          if starts_with "CYP-OK " l then
            Hashtbl.replace status (int_of_string (String.sub l 7 (String.length l - 7))) Ok
          else if starts_with "CYP-KO " l then
            Hashtbl.replace status
              (int_of_string (String.sub l 7 (String.length l - 7))) (Ko ("", "")))
        (lines out)
    else
      match Option.bind (error_line out) (obligation_at starts) with
      | Some n ->
          (* the message without its position: the same formula rejected
             again in a later step's context is the earlier step's fault *)
          let key = Str.global_replace (Str.regexp "File .*\n") "" out in
          let msg =
            if List.mem key !seen then
              "This step does not type-check because an earlier step does not: see the first Rocq error above."
            else (seen := key :: !seen; out) in
          Hashtbl.replace status n (Err msg);
          loop (List.filter (fun o -> o.num <> n) obs)
      | None ->
          (* the preamble itself fails: every obligation gets the message *)
          List.iter (fun o -> Hashtbl.replace status o.num (Err out)) obs in
  loop obs;
  (* for each failing obligation: its goal and Rocq's message *)
  List.iter (fun o ->
      match Hashtbl.find_opt status o.num with
      | Some (Ko _) ->
          let src = Printf.sprintf
              "%s\nGoal %s.\nProof. intros. idtac \"CYP-GOAL\". Show.\n%s.\nQed.\n"
              h.require (goal_of o) (step_tac h o) in
          let _, out = compile (Printf.sprintf "cyp_ko_%d" o.num) src in
          let goal, msg =
            match Str.search_forward (Str.regexp_string "CYP-GOAL") out 0 with
            | p ->
                let rest = String.sub out (p + 8) (String.length out - p - 8) in
                (match Str.search_forward (Str.regexp "^File ") rest 0 with
                 | q -> (trim (String.sub rest 0 q),
                         trim (String.sub rest q (String.length rest - q)))
                 | exception Not_found -> (trim rest, ""))
            | exception Not_found -> ("", trim out) in
          Hashtbl.replace status o.num (Ko (goal, msg))
      | _ -> ()) obs;
  status

(* ------------------------------------------------------------------ *)
(* The outputs                                                         *)

(* The proof as Rocq goals, for reading. *)
let v_file h obs =
  let b = Buffer.create 4096 in
  Buffer.add_string b ("(* Generated by cyp: one goal per step. *)\n" ^ h.require ^ "\n\n");
  List.iter (fun o ->
      Printf.bprintf b "(* step %d *)\nGoal %s.\nProof. %s. %s. Qed.\n\n"
        o.owner (goal_of o) (intro_ctx o) (step_tac h o)) obs;
  Buffer.contents b

(* The colour of a step: all its obligations proved, one failed, or
   nothing to check. *)
let step_status obs status id =
  let mine = List.filter (fun o -> o.owner = id) obs in
  let sts = List.map (fun o ->
      Option.value (Hashtbl.find_opt status o.num) ~default:(Err "not run")) mine in
  if mine = [] then (`None, [])
  else if List.for_all (( = ) Ok) sts then (`Ok, [])
  else (`Ko, List.filter (( <> ) Ok) sts)

(* A piece back as Markdown, as the author wrote it (without role tags). *)
let md_pieces ps =
  String.concat "" (List.map (function
      | Text t -> t
      | Formula (_, f) -> "`" ^ f ^ "`"
      | By t -> "*by " ^ t ^ "*") ps)

let mark = function `Ok -> "✅" | `Ko -> "❌" | `None -> "▫️"

(* Under a failing step: its goal and Rocq's message, folded, indented by
   [pad] to stay inside the list item. *)
let md_details pad sts =
  let block title body =
    let body = String.concat "\n" (List.map (fun l -> pad ^ l) (lines body)) in
    Printf.sprintf "\n%s<details><summary>%s</summary>\n\n%s```\n%s\n%s```\n\n%s</details>\n"
      pad title pad body pad pad in
  String.concat "" (List.map (function
      | Ko (goal, msg) -> block "not proved" (goal ^ "\n\n" ^ msg)
      | Err msg -> block "Rocq error" msg
      | Ok -> "") sts)

let md_file h props obs status =
  let b = Buffer.create 8192 in
  Printf.bprintf b "<!-- checked by cyp; prelude: %s -->\n\n"
    (String.concat " " (lines h.require));
  let rec steps depth st =
    List.iter (fun s ->
        let k, sts = step_status obs status s.id in
        let pad = String.make (2 * depth) ' ' in
        Printf.bprintf b "%s- %s %s\n%s" pad (mark k) (md_pieces s.pieces)
          (md_details (pad ^ "  ") sts);
        steps (depth + 1) s.children) st in
  List.iter (fun p ->
      let k, sts = step_status obs status p.pid in
      Printf.bprintf b "# %s\n\n%s %s\n%s\n" p.name (mark k)
        (md_pieces p.statement) (md_details "" sts);
      steps 0 p.steps;
      Buffer.add_string b "\n") props;
  Buffer.contents b

(* The result for an editor: for each step (and statement), its lines,
   its status, the formulas with their roles, and for a failure the goal
   and Rocq's message. *)
let json_string s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter (function
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | '\n' -> Buffer.add_string b "\\n"
      | '\r' -> ()
      | '\t' -> Buffer.add_string b "\\t"
      | c when Char.code c < 32 -> Printf.bprintf b "\\u%04x" (Char.code c)
      | c -> Buffer.add_char b c) s;
  Buffer.add_char b '"';
  Buffer.contents b

let json_file props obs status =
  let items = ref [] in
  let one id first last ps =
    let k, sts = step_status obs status id in
    let st = match k with `Ok -> "ok" | `Ko -> "ko" | `None -> "none" in
    let formulas = List.filter_map (function
        | Formula (r, f) ->
            let r = match r with
              | Var -> "var" | Hyp -> "hyp" | Claim -> "claim" | Fact -> "fact" in
            Some (Printf.sprintf "{\"role\":\"%s\",\"text\":%s}" r (json_string f))
        | _ -> None) ps in
    let msgs = List.filter_map (function
        | Ko (goal, msg) -> Some (goal ^ "\n\n" ^ msg)
        | Err msg -> Some msg
        | Ok -> None) sts in
    items := Printf.sprintf
        "{\"first\":%d,\"last\":%d,\"status\":\"%s\",\"formulas\":[%s],\"message\":%s}"
        first last st (String.concat "," formulas)
        (json_string (String.concat "\n\n" msgs)) :: !items in
  let rec steps st =
    List.iter (fun s -> one s.id s.first s.last s.pieces; steps s.children) st in
  List.iter (fun p -> one p.pid p.sfirst p.slast p.statement; steps p.steps) props;
  "{\"steps\":[" ^ String.concat ",\n" (List.rev !items) ^ "]}\n"

(* ------------------------------------------------------------------ *)

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  let json = List.mem "--json" args in
  match List.filter (( <> ) "--json") args with
  | [ md ] ->
      let h, props = parse ~dir:(Filename.dirname md) (read_file md) in
      flags := h.flags;
      let obs = obligations h props in
      (* the cache: a step proved before, with the same preamble, goal and
         tactic, is not checked again *)
      let cache_file = Filename.remove_extension md ^ ".cyp-cache" in
      let key o = Digest.to_hex (Digest.string
          (String.concat "\000" [h.require; h.flags; goal_of o; step_tac h o])) in
      let cached =
        try List.filter (( <> ) "") (lines (read_file cache_file)) with _ -> [] in
      let fresh, known = List.partition (fun o -> not (List.mem (key o) cached)) obs in
      let status = if fresh = [] then Hashtbl.create 1 else check h fresh in
      List.iter (fun o -> Hashtbl.replace status o.num Ok) known;
      write_file cache_file (String.concat "\n" (List.filter_map (fun o ->
          if Hashtbl.find_opt status o.num = Some Ok then Some (key o) else None) obs) ^ "\n");
      if known <> [] then
        Printf.eprintf "cyp: %d step(s) unchanged since they were proved, not checked again\n%!"
          (List.length known);
      let base = Filename.remove_extension md in
      write_file (base ^ ".cyp.v") (v_file h obs);
      write_file (base ^ ".checked.md") (md_file h props obs status);
      if json then print_string (json_file props obs status) else
      let count p = List.length (List.filter p obs) in
      let st o = Hashtbl.find_opt status o.num in
      Printf.printf "%s: %d steps, %d proved, %d not proved, %d errors\n"
        (base ^ ".checked.md") (List.length obs)
        (count (fun o -> st o = Some Ok))
        (count (fun o -> match st o with Some (Ko _) -> true | _ -> false))
        (count (fun o -> match st o with Some (Err _) | None -> true | _ -> false))
  | _ -> prerr_endline "usage: cyp [--json] proof.md"; exit 2
