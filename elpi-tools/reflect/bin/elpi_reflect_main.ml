(* elpi-reflect [-I DIR].. [-D VAR].. FILE..
   prints the program made of FILE.. as Elpi facts (see ../README.md). *)

let usage = "elpi-reflect [-I DIR].. [-D VAR].. FILE..\n\
             Prints the declarations, rules and CHR rules of the files as Elpi data."

let () =
  let paths = ref [] and defines = ref [] and files = ref [] in
  let spec = [
    ("-I", Arg.String (fun d -> paths := !paths @ [ d ]), "DIR  search accumulated files in DIR");
    ("-D", Arg.String (fun v -> defines := v :: !defines), "VAR  define VAR (for :if \"VAR\" rules)");
  ] in
  Arg.parse spec (fun f -> files := !files @ [ f ]) usage;
  if !files = [] then (prerr_endline usage; exit 2);
  match Elpi_reflect.Reflect.reflect_files ~paths:!paths ~defines:!defines !files with
  | text -> print_string text
  | exception Elpi_reflect.Reflect.Error msg -> prerr_endline msg; exit 1
