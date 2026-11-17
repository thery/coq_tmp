(* cyp: colour a proof written in Markdown by checking each of its steps
   with Rocq.

   cyp proof.md  writes  proof.v    (one goal per step)
                         proof.html (the proof, each step coloured)

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

let html_escape s =
  let b = Buffer.create (String.length s) in
  String.iter (function
    | '<' -> Buffer.add_string b "&lt;"
    | '>' -> Buffer.add_string b "&gt;"
    | '&' -> Buffer.add_string b "&amp;"
    | '"' -> Buffer.add_string b "&quot;"
    | c -> Buffer.add_char b c) s;
  Buffer.contents b

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
}

type prop = {
  name : string;
  pid : int;                      (* the id of the statement *)
  statement : piece list;
  steps : step list;
}

type header = {
  require : string;               (* the Rocq preamble *)
  default_by : string;            (* the default justification *)
  timeout : int;                  (* seconds per step *)
}

(* Words that give the role of the formulas that follow them. *)
let role_words = [
  "let", Var;
  "if", Hyp; "assume", Hyp; "suppose", Hyp; "where", Hyp;
  "from", Fact; "using", Fact; "since", Fact; "because", Fact;
  "then", Claim; "show", Claim; "prove", Claim; "have", Claim;
  "get", Claim; "thus", Claim; "hence", Claim; "so", Claim;
  "written as", Claim; "is", Claim; "obtain", Claim; "deduce", Claim;
]

(* The role given by the last role word of [txt], if any. *)
let role_of_text txt =
  let t = " " ^ String.lowercase_ascii txt ^ " " in
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
      | None -> ()) role_words;
  Option.map snd !best

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
    | s :: rest -> let f = Formula (!role, s) in f :: go (i + 1) rest in
  let ps = go 0 parts in
  match by with Some t -> ps @ [By t] | None -> ps

let counter = ref 0
let fresh () = incr counter; !counter

(* A list item starts with "- ", "* " or "1. ". *)
let item_re = Str.regexp "^\\(-\\|\\*\\|[0-9]+\\.\\) +"

(* Parse the list items of a proof: each item is (indent, text). *)
let rec build_steps items =
  match items with
  | [] -> []
  | (ind, txt) :: rest ->
      let rec split acc = function
        | (i, t) :: r when i > ind -> split ((i, t) :: acc) r
        | r -> (List.rev acc, r) in
      let sub, rest = split [] rest in
      let id = fresh () in
      { id; pieces = pieces_of_text ~default:Claim txt;
        children = build_steps sub } :: build_steps rest

let parse src =
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
  } in
  let h =
    let scope = get "scope" "" in
    if scope = "" then h
    else { h with require = h.require ^ "\nOpen Scope " ^ scope ^ "." } in
  (* the propositions, each starting with a line "# name" *)
  let props = ref [] in
  let cur = ref None in
  let flush () =
    match !cur with
    | Some (name, stmt, items) ->
        let pid = fresh () in
        let stmt_text = String.concat " " (List.rev stmt) in
        let items = List.rev items in
        props := { name; pid;
                   statement = pieces_of_text ~default:Claim stmt_text;
                   steps = build_steps items } :: !props
    | None -> () in
  List.iter (fun l ->
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
              cur := Some (n, stmt, (ind, txt) :: items)
            else if t = "" then ()
            else (match items with
                | (i, txt) :: r when ind > 0 ->
                    cur := Some (n, stmt, (i, txt ^ " " ^ t) :: r)
                | _ when items = [] -> cur := Some (n, t :: stmt, items)
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

(* Words that make a step go backwards: its formula replaces the goal. *)
let backward_words = [ "suffices"; "enough"; "equivalent to prove";
                       "written as"; "amounts to"; "reduces to" ]

let is_backward ps =
  let txt = String.concat " " (List.filter_map (function
      | Text t -> Some (String.lowercase_ascii t) | _ -> None) ps) in
  List.exists (contains txt) backward_words

let obligations h props =
  let obs = ref [] in
  let n = ref 0 in
  let add owner vars hyps concl tac =
    incr n;
    obs := { num = !n; owner; vars; hyps; concl; tac } :: !obs in
  (* the steps [st] prove [goal] in the context [hyps]; the last
     obligation, that [goal] follows, belongs to [owner] *)
  let rec level owner owner_tac vars hyps goal st =
    let hyps, goal =
      List.fold_left (fun (hyps, goal) s ->
          match conj (formulas Claim s.pieces) with
          | None -> (hyps, goal)      (* a comment: nothing to check *)
          | Some c ->
              let tac = by_of h s.pieces in
              if is_backward s.pieces then begin
                (* the new goal [c] implies the old one *)
                add s.id vars (hyps @ [c]) goal tac;
                if s.children <> [] then
                  level s.id (by_of h []) vars hyps c s.children;
                (hyps, c)
              end else begin
                if s.children <> [] then level s.id tac vars hyps c s.children
                else add s.id vars hyps c tac;
                (hyps @ [c], goal)
              end) (hyps, goal) st in
    add owner vars hyps goal owner_tac in
  List.iter (fun p ->
      let vars = formulas Var p.statement in
      let hyps = formulas Hyp p.statement in
      match conj (formulas Claim p.statement) with
      | None -> ()
      | Some goal -> level p.pid (by_of h p.statement) vars hyps goal p.steps)
    props;
  List.rev !obs

(* The Rocq goal of an obligation. *)
let goal_of o =
  let binders = String.concat " " (List.map (fun v -> "(" ^ v ^ ")") o.vars) in
  let body =
    String.concat " -> " (List.map (fun f -> "(" ^ f ^ ")") (o.hyps @ [o.concl])) in
  if binders = "" then body else "forall " ^ binders ^ ", " ^ body

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
let compile name src =
  let f = Filename.concat tmpdir (name ^ ".v") in
  let out = Filename.concat tmpdir (name ^ ".out") in
  write_file f src;
  let code = Sys.command (Printf.sprintf "cd %s && %s %s > %s 2>&1"
                            (Filename.quote tmpdir) rocq
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
        "Goal %s.\nProof. intros.\ntryif solve [timeout %d (%s)] then idtac \"CYP-OK %d\" else idtac \"CYP-KO %d\".\nAbort.\n"
        (goal_of o) h.timeout o.tac o.num o.num) obs;
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
          Hashtbl.replace status n (Err out);
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
              "%s\nGoal %s.\nProof. intros. idtac \"CYP-GOAL\". Show.\nsolve [timeout %d (%s)].\nQed.\n"
              h.require (goal_of o) h.timeout o.tac in
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
      Printf.bprintf b "(* step %d *)\nGoal %s.\nProof. intros. %s. Qed.\n\n"
        o.owner (goal_of o) o.tac) obs;
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

let css = {|
body { font-family: Georgia, serif; max-width: 52em; margin: 2em auto;
       padding: 0 1em; line-height: 1.5; color: #222; background: #fff; }
h1 { font-size: 1.3em; border-bottom: 1px solid #ccc; }
code { font-family: Menlo, Consolas, monospace; font-size: 0.92em;
       padding: 0 0.2em; border-radius: 3px; }
.hyp { background: #e3ecff; color: #1a3d8f; }
.fact { background: #f0e6ff; color: #5b2a86; }
.var { background: #eee; }
.ok .claim, .ok > .stmt .claim { background: #dff5df; color: #14601e; }
.ko .claim, .ko > .stmt .claim { background: #fde0e0; color: #9b1c1c; }
.none .claim { background: #eee; }
.by { font-family: Menlo, Consolas, monospace; font-size: 0.8em;
      color: #777; margin-left: 0.5em; }
li { margin: 0.3em 0; }
.mark { display: inline-block; width: 1.2em; font-weight: bold; }
.ok > .mark { color: #14601e; }
.ko > .mark { color: #9b1c1c; }
.none > .mark { color: #aaa; }
details { margin: 0.3em 0 0.6em 1.2em; }
summary { cursor: pointer; color: #9b1c1c; font-size: 0.9em; }
pre { background: #f7f7f7; padding: 0.6em; overflow-x: auto;
      font-size: 0.85em; white-space: pre-wrap; }
.legend { font-size: 0.85em; color: #555; }
|}

let html_pieces ps =
  String.concat "" (List.map (function
      | Text t -> html_escape t
      | Formula (r, f) ->
          let c = match r with
            | Var -> "var" | Hyp -> "hyp" | Claim -> "claim" | Fact -> "fact" in
          Printf.sprintf "<code class=\"%s\">%s</code>" c (html_escape f)
      | By t -> Printf.sprintf "<span class=\"by\">by %s</span>" (html_escape t))
      ps)

let html_details sts =
  String.concat "" (List.map (function
      | Ko (goal, msg) ->
          Printf.sprintf "<details><summary>not proved</summary><pre>%s</pre><pre>%s</pre></details>"
            (html_escape goal) (html_escape msg)
      | Err msg ->
          Printf.sprintf "<details><summary>Rocq error</summary><pre>%s</pre></details>"
            (html_escape msg)
      | Ok -> "") sts)

let html_file title props obs status =
  let b = Buffer.create 8192 in
  let cls = function `Ok -> "ok" | `Ko -> "ko" | `None -> "none" in
  let mark = function `Ok -> "&#10003;" | `Ko -> "&#10007;" | `None -> "&middot;" in
  let rec steps st =
    Buffer.add_string b "<ul style=\"list-style:none; padding-left:1.2em\">\n";
    List.iter (fun s ->
        let k, sts = step_status obs status s.id in
        Printf.bprintf b "<li class=\"%s\"><span class=\"mark\">%s</span>%s%s"
          (cls k) (mark k) (html_pieces s.pieces) (html_details sts);
        if s.children <> [] then steps s.children;
        Buffer.add_string b "</li>\n") st;
    Buffer.add_string b "</ul>\n" in
  Printf.bprintf b
    "<!doctype html>\n<html><head><meta charset=\"utf-8\">\n<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n<title>%s</title><style>%s</style></head><body>\n"
    (html_escape title) css;
  Buffer.add_string b
    "<p class=\"legend\"><code class=\"hyp\">hypothesis</code> <code class=\"fact\">fact used</code> claim: <span class=\"ok\"><code class=\"claim\">proved</code></span> <span class=\"ko\"><code class=\"claim\">not proved</code></span></p>\n";
  List.iter (fun p ->
      let k, sts = step_status obs status p.pid in
      Printf.bprintf b "<h1>%s</h1>\n<div class=\"%s\"><p class=\"stmt\"><span class=\"mark\">%s</span>%s</p>%s"
        (html_escape p.name) (cls k) (mark k) (html_pieces p.statement)
        (html_details sts);
      steps p.steps;
      Buffer.add_string b "</div>\n") props;
  Buffer.add_string b "</body></html>\n";
  Buffer.contents b

(* ------------------------------------------------------------------ *)

let () =
  match Array.to_list Sys.argv with
  | [ _; md ] ->
      let h, props = parse (read_file md) in
      let obs = obligations h props in
      let status = check h obs in
      let base = Filename.remove_extension md in
      write_file (base ^ ".v") (v_file h obs);
      write_file (base ^ ".html")
        (html_file (Filename.basename base) props obs status);
      let count p = List.length (List.filter p obs) in
      let st o = Hashtbl.find_opt status o.num in
      Printf.printf "%s: %d steps, %d proved, %d not proved, %d errors\n"
        (base ^ ".html") (List.length obs)
        (count (fun o -> st o = Some Ok))
        (count (fun o -> match st o with Some (Ko _) -> true | _ -> false))
        (count (fun o -> match st o with Some (Err _) | None -> true | _ -> false))
  | _ -> prerr_endline "usage: cyp proof.md"; exit 2
