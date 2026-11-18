(* cyp [--json | --conditions] proof.md: check a cyp proof with Cyp File.

   The driver of cyp.  It keeps no semantics: from the header of the proof
   it writes a small .v file (the header's require: line, its rule files,
   then  CypFile "proof.md".), runs rocq c on it, and prints cyp's
   messages (with --json: the file proof.cyp.json, for the editor; with
   --conditions: every condition of the text with its context, nothing
   tried, as #[bare] CypFile prints them).  Cyp
   File writes proof.checked.md and proof.cyp.json next to the proof.

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

let cyp_lib () =
  match Sys.getenv_opt "CYP_LIB" with
  | Some d -> d
  | None -> prerr_endline "cyp: set CYP_LIB to the directory of the cyp library (vernac/)"; exit 2

let main ~json ~conditions md =
  let md = absolute (Sys.getcwd ()) md in
  let dir = Filename.dirname md in
  let h = header (read_file md) in
  let tmp = temp_dir () in
  let rules = List.mapi (fun k f -> (k, absolute dir f)) (words (field h "rules")) in
  let rule_lines =
    List.concat_map (fun (k, f) ->
        if Filename.check_suffix f ".elpi" then begin
          let link = Filename.concat tmp (Printf.sprintf "rules%d.elpi" k) in
          Unix.symlink f link;
          [ Printf.sprintf "From CypRules Extra Dependency \"rules%d.elpi\" as cyp_rules%d." k k;
            Printf.sprintf "Elpi Accumulate cyp.db File cyp_rules%d." k ]
        end else [ read_file f ]) rules in
  let scope = match field h "scope" with "" -> [] | s -> [ "Open Scope " ^ s ^ "." ] in
  let v =
    [ field h "require"; "From CypV Require Import Cyp." ] @ scope @ rule_lines
    @ [ Printf.sprintf "%sCypFile %S." (if conditions then "#[bare] " else "") md ] in
  let src = Filename.concat tmp "cyp_check.v" in
  write_file src (String.concat "\n" v ^ "\n");
  let flags = relative_flags dir (words (expand (field h "flags"))) in
  let out = Filename.concat tmp "cyp_check.out" in
  let cmd =
    String.concat " " (List.map Filename.quote
      ([ "rocq"; "c"; "-Q"; cyp_lib (); "CypV"; "-Q"; tmp; "CypRules" ] @ flags @ [ src ])) in
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
  else
    List.iter (fun l ->
        if Str.string_match (Str.regexp ".*\\(cyp:\\|Error\\)") l 0 then print_endline l)
      (String.split_on_char '\n' (read_file out));
  (* the temporary directory and its files are not kept *)
  ignore (Sys.command ("rm -rf " ^ Filename.quote tmp));
  code

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [ "--json"; md ] -> exit (main ~json:true ~conditions:false md)
  | [ "--conditions"; md ] -> exit (main ~json:false ~conditions:true md)
  | [ md ] -> exit (main ~json:false ~conditions:false md)
  | _ -> prerr_endline "usage: cyp [--json | --conditions] proof.md"; exit 2
