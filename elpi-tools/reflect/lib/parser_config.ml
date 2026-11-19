(* The configuration of Elpi's parser (the argument of
   Elpi_parser.Parse.Make) used by elpi-reflect and elpi-debug, for
   Elpi 4.0.0 and Elpi >= 4.1.0.

   Elpi 4.0.0 needs [versions] and [resolver]; Elpi 4.1.0 adds [reader],
   [package_dir], [plugin] and [root_of_dir].  A structure may have more
   values than the signature it is matched against, so this one structure
   serves both versions: with Elpi 4.0.0 the last four values are unused.

   The values are those of the parser that [Elpi.API.Setup.init] makes when
   it is given a [~file_resolver] and no [~packages], as the tools'
   own calls of [Setup.init] are: a file read by these parsers is then read
   in the same way by the compiler that the tools run afterwards. *)

(* [accumulate "+pkg..."] is rejected: the tools do not load packages *)
let Elpi_util.Util.ErrorFun { error; _ } = Elpi_util.Util.error_fun ~component:"elpi-tools"

module Make (C : sig val paths : string list end) = struct
  (* the versions of the [:if] conditions: none *)
  let versions = Elpi_util.Util.StrMap.empty

  (* the file named by [accumulate "unit"]: looked up in the current
     directory, then in the search paths (-I) *)
  let resolver = Elpi.API.Parse.std_resolver ~paths:C.paths ()

  (* the text of a file, read from the disk; Failure if it cannot be read
     (the contract and the code of Elpi 4.1's Parse.std_reader) *)
  let reader f =
    try
      let ic = open_in_bin f in
      Fun.protect ~finally:(fun () -> close_in ic)
        (fun () -> really_input_string ic (in_channel_length ic))
    with Sys_error msg -> raise (Failure msg)

  (* [accumulate "+pkg/path"]: the directory of a package; packages are
     disabled *)
  let package_dir ~pkg =
    error (Printf.sprintf "accumulate \"+%s\": elpi-tools does not load packages" pkg)

  (* [accumulate "+pkg"]: no plugin is loaded, so the parser asks
     [package_dir] for the stub of the plugin, which fails as above *)
  let plugin ~pkg:_ = None

  (* [accumulate "+/path"]: the root of the project; there is none *)
  let root_of_dir ~dir:_ =
    error "accumulate \"+/...\": elpi-tools does not load packages"
end
