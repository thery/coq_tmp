(* cyp [--time] [--stats] [--json | --conditions | --only N | --extract N] proof.md:
   check a cyp proof with Cyp File.

   The driver of cyp.  It keeps no semantics: from the header of the proof
   it writes a small .v file (the header's require: line, its rule files,
   then  CypFile "proof.md".), runs rocq c on it, and prints cyp's
   messages (with --json: the file proof.cyp.json, for the editor; with
   --conditions: every condition of the text with its context, nothing
   tried, as #[bare] CypFile prints them; with --time: the time of each
   condition and how it was closed, then the slowest, as #[time] CypFile
   prints them).  Cyp
   File writes proof.checked.md and proof.cyp.json next to the proof.

   To debug a text (../README.md, "Debugging a text"; vernac/elpi/stats.elpi):
   --stats (#[stats="univ"]): the size of the proof of each condition, the
   heaviest, the sizes of the whole proof; cyp prints the universe state
   after each of them, and the driver turns it into counts of sort
   variables and universe levels (univ_counts, print_stats, below);
   --only N (#[only="N"]): the conditions built as with --conditions, only
   N tried (with --time or --stats: its line); --extract N
   (#[extract="N"]): the same, and condition N written as a Rocq file
   proof_cN.v next to the proof (dots of N as _).  With --only and
   --extract nothing else is written.

   Header fields used here: require: (Rocq text), rules: (files .elpi,
   added to cyp.db, or .v, copied in), flags: (options of rocq c; the
   directories of -Q, -R and -I are relative to the proof, ${NAME} is the
   environment variable NAME), scope: (opened).
   The cyp library (vernac/, compiled) is found in the directory given by
   CYP_LIB. *)

let read_file f =
  let ic = open_in_bin f in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic; s

let write_file f s =
  let oc = open_out_bin f in
  output_string oc s; close_out oc

let trim = String.trim

let absolute d f = if Filename.is_relative f then Filename.concat d f else f

(* the fields of the header, between the first two lines "---" *)
let header text =
  match String.split_on_char '\n' text with
  | l :: rest when trim l = "---" ->
      let rec take acc = function
        | l :: r when trim l <> "---" ->
            let acc =
              match String.index_opt l ':' with
              | Some i ->
                  (trim (String.sub l 0 i),
                   trim (String.sub l (i + 1) (String.length l - i - 1))) :: acc
              | None -> acc in
            take acc r
        | _ -> acc in
      take [] rest
  | _ -> []

let field h k = Option.value (List.assoc_opt k h) ~default:""

let words s = List.filter (( <> ) "") (String.split_on_char ' ' s)

(* ${NAME} in a header field: the environment variable NAME, so that a
   proof does not name the directories of one machine *)
let expand s =
  Str.global_substitute (Str.regexp "\\${\\([A-Za-z_][A-Za-z0-9_]*\\)}")
    (fun s ->
      let v = Str.matched_group 1 s in
      match Sys.getenv_opt v with
      | Some x -> x
      | None -> prerr_endline ("cyp: the variable " ^ v ^ " of the header is not set"); exit 2)
    s

(* -Q, -R and -I directories relative to the directory of the proof *)
let rec relative_flags d = function
  | ("-Q" | "-R" | "-I" as o) :: dir :: r -> o :: absolute d dir :: relative_flags d r
  | x :: r -> x :: relative_flags d r
  | [] -> []

(* a fresh temporary directory *)
let temp_dir () =
  let f = Filename.temp_file "cyp-" "" in
  Sys.remove f; Unix.mkdir f 0o755; f

(* the directory of the cyp library, resolved (no "..", no link), so that
   the directories next to it are found from it by name *)
let cyp_lib () =
  match Sys.getenv_opt "CYP_LIB" with
  | Some d -> (try Unix.realpath d with Unix.Unix_error _ -> d)
  | None -> prerr_endline "cyp: set CYP_LIB to the directory of the cyp library (vernac/)"; exit 2

(* the language data (lexicon/, shared with xtext): CYP_LEXICON, or the
   directory lexicon/ of the repository that holds CYP_LIB (cyp/vernac) *)
let lexicon () =
  match Sys.getenv_opt "CYP_LEXICON" with
  | Some d -> d
  | None -> Filename.concat (Filename.dirname (Filename.dirname (cyp_lib ()))) "lexicon"

(* the format of proof texts (prooftext/, shared with xtext): CYP_PROOFTEXT,
   or the directory prooftext/ next to lexicon/ *)
let prooftext () =
  match Sys.getenv_opt "CYP_PROOFTEXT" with
  | Some d -> d
  | None -> Filename.concat (Filename.dirname (lexicon ())) "prooftext"

(* --stats: the universe state that cyp prints after each condition (between
   the lines "cyp-univ-begin LABEL" and "cyp-univ-end LABEL", #[stats="univ"],
   vernac/elpi/stats.elpi), reduced to two counts: its sort variables (the
   lines "αN := ..." or "αN >= ..." of its SORTS: part) and its universe
   levels (the names Lib.Name.N before that part, each counted once) *)
let univ_counts lines =
  let sort_re = Str.regexp ".*α[0-9]+ \\(>=\\|:=\\)" in
  let level_re = Str.regexp "[A-Za-z_][A-Za-z0-9_']*\\(\\.[A-Za-z_][A-Za-z0-9_']*\\)*\\.[0-9]+" in
  let levels = Hashtbl.create 1024 in
  let sorts = ref 0 and in_sorts = ref false and over = ref false in
  List.iter (fun l ->
      if !over then ()
      else if Str.string_match (Str.regexp " *WEAK CONSTRAINTS:") l 0 then over := true
      else if Str.string_match (Str.regexp " *SORTS:") l 0 then in_sorts := true
      else if !in_sorts then (if Str.string_match sort_re l 0 then incr sorts)
      else begin
        let rec scan i =
          match Str.search_forward level_re l i with
          | j -> Hashtbl.replace levels (Str.matched_string l) (); scan (j + String.length (Str.matched_string l))
          | exception Not_found -> () in
        scan 0
      end) lines;
  (!sorts, Hashtbl.length levels)

(* --stats: Rocq's output, each line "cyp: stats ..." followed by the counts
   of the universe state after it, and what each condition added to it;
   then the ten conditions that added the most sort variables *)
let print_stats out =
  let ic = open_in_bin out in
  let pending = ref None and block = ref [] and in_block = ref false in
  let prev = ref (0, 0) and added = ref [] in
  let begin_re = Str.regexp "^cyp-univ-begin \\(.*\\)$" and end_re = Str.regexp "^cyp-univ-end" in
  (try
     while true do
       let l = input_line ic in
       if Str.string_match begin_re l 0 then (in_block := true; block := [])
       else if Str.string_match end_re l 0 then begin
         in_block := false;
         let (s, v) = univ_counts (List.rev !block) in
         let (s0, v0) = !prev in
         prev := (s, v);
         (match !pending with
          | Some p ->
              let id = match String.index_from_opt p 11 ' ' with
                | Some i -> String.sub p 11 (i - 11) | None -> "" in
              Printf.printf "%s | sorts=%d (+%d) levels=%d (+%d)\n" p s (s - s0) v (v - v0);
              added := (id, s - s0, v - v0) :: !added
          | None -> ());
         pending := None
       end
       else if !in_block then block := l :: !block
       else if Str.string_match (Str.regexp ".*\\(cyp:\\|Error\\)") l 0 then begin
         (* a line of a condition, or of the whole proof, waits for its counts *)
         Option.iter print_endline !pending; pending := None;
         if Str.string_match (Str.regexp "cyp: stats ") l 0
            && not (Str.string_match (Str.regexp "cyp: stats of the ") l 0)
         then pending := Some l else print_endline l end
     done
   with End_of_file -> ());
  Option.iter print_endline !pending;
  close_in ic;
  let steps = List.filter (fun (id, _, _) -> id <> "type-check" && id <> "definition") !added in
  let sorted = List.stable_sort (fun (_, a, _) (_, b, _) -> compare b a) (List.rev steps) in
  if sorted <> [] then begin
    print_endline "cyp: stats the conditions that added the most sort variables:";
    List.iteri (fun k (id, s, v) ->
        if k < 10 then Printf.printf "cyp:   %s  sorts +%d  levels +%d\n" id s v) sorted
  end

let main ~json ~conditions ~time ~stats ~target md =
  let md = absolute (Sys.getcwd ()) md in
  let dir = Filename.dirname md in
  let h = header (read_file md) in
  let tmp = temp_dir () in
  let rules = List.mapi (fun k f -> (k, absolute dir f)) (words (field h "rules")) in
  let src = Filename.concat tmp "cyp_check.v" in
  let scope = match field h "scope" with "" -> [] | s -> [ "Open Scope " ^ s ^ "." ] in
  let head = [ field h "require"; "From CypV Require Import Cyp." ] @ scope in
  (* the number of lines of a list of lines (each may hold newlines) *)
  let count ls =
    List.fold_left (fun n l ->
        n + 1 + List.length (String.split_on_char '\n' l) - 1) 0 ls in
  (* each rule file: .elpi, accumulated in cyp.db; .v, copied in, after a
     clause copied-lines that gives the place of its lines in the file
     (Cyp.v: a CypJustification there is declared at its line of the
     rule file, for the links) *)
  let rule_lines =
    List.fold_left (fun acc (k, f) ->
        if Filename.check_suffix f ".elpi" then begin
          let link = Filename.concat tmp (Printf.sprintf "rules%d.elpi" k) in
          Unix.symlink f link;
          acc @ [ Printf.sprintf "From CypRules Extra Dependency \"rules%d.elpi\" as cyp_rules%d." k k;
                  Printf.sprintf "Elpi Accumulate cyp.db File cyp_rules%d." k ]
        end else begin
          let text = read_file f in
          let first = count (head @ acc) + 2 in
          let last = first + List.length (String.split_on_char '\n' text) - 1 in
          acc @ [ Printf.sprintf "Elpi Accumulate cyp.db lp:{{ copied-lines %S %d %d %S. }}."
                    src first last f;
                  text ]
        end) [] rules in
  (* the attributes of CypFile: #[bare], #[time], #[stats="univ"],
     #[only="N"], #[extract="N"] *)
  let attributes =
    (if conditions then [ "bare" ] else []) @ (if time then [ "time" ] else [])
    @ (if stats then [ "stats=\"univ\"" ] else [])
    @ (match target with
       | `Only n -> [ Printf.sprintf "only=%S" n ]
       | `Extract n -> [ Printf.sprintf "extract=%S" n ]
       | `All -> []) in
  let v =
    head @ rule_lines
    @ [ Printf.sprintf "%sCypFile %S."
          (if attributes = [] then "" else "#[" ^ String.concat ", " attributes ^ "] ")
          md ] in
  write_file src (String.concat "\n" v ^ "\n");
  let flags = relative_flags dir (words (expand (field h "flags"))) in
  let out = Filename.concat tmp "cyp_check.out" in
  let cmd =
    String.concat " " (List.map Filename.quote
      ([ "rocq"; "c"; "-Q"; cyp_lib (); "CypV"; "-Q"; lexicon (); "Lexicon"; "-Q"; prooftext (); "ProofText";
         "-Q"; tmp; "CypRules" ] @ flags @ [ src ])) in
  (* run in the directory of the proof, where the caches of lia and nia
     (.lia.cache, .nia.cache) are kept from one run to the next *)
  let code = Sys.command (Printf.sprintf "cd %s && %s > %s 2>&1"
                            (Filename.quote dir) cmd (Filename.quote out)) in
  let js = Filename.remove_extension md ^ ".cyp.json" in
  if json && Sys.file_exists js then print_string (read_file js)
  else if conditions then
    (* Rocq's output, without its locations and warnings *)
    List.iter (fun l ->
        if not (Str.string_match (Str.regexp "^File \\|^Warning\\|^\\[") l 0)
        then print_endline l)
      (String.split_on_char '\n' (read_file out))
  else if stats then print_stats out
  else
    List.iter (fun l ->
        if Str.string_match (Str.regexp ".*\\(cyp:\\|Error\\)") l 0 then print_endline l)
      (String.split_on_char '\n' (read_file out));
  (* the temporary directory and its files are not kept *)
  ignore (Sys.command ("rm -rf " ^ Filename.quote tmp));
  code

let usage () =
  prerr_endline
    "usage: cyp [--time] [--stats] [--json | --conditions | --only NODE | --extract NODE] proof.md";
  exit 2

let () =
  let rec parse (json, conditions, time, stats, target) = function
    | "--time" :: r -> parse (json, conditions, true, stats, target) r
    | "--stats" :: r -> parse (json, conditions, time, true, target) r
    | "--json" :: r -> parse (true, conditions, time, stats, target) r
    | "--conditions" :: r -> parse (json, true, time, stats, target) r
    | "--only" :: n :: r -> parse (json, conditions, time, stats, `Only n) r
    | "--extract" :: n :: r -> parse (json, conditions, time, stats, `Extract n) r
    | [ md ] when md <> "" && md.[0] <> '-' ->
        let modes = List.length (List.filter Fun.id
          [ json; conditions; target <> `All ]) in
        if modes > 1 then usage ();
        exit (main ~json ~conditions ~time ~stats ~target md)
    | _ -> usage () in
  parse (false, false, false, false, `All) (List.tl (Array.to_list Sys.argv))
