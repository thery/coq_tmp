(* The messages of the Debug Adapter Protocol that the adapter reads and
   writes (https://microsoft.github.io/debug-adapter-protocol/), as JSON.
   The sequence numbers of the adapter's own messages are given by the
   caller (Session). *)

type json = Yojson.Safe.t

(* A request of the client: its sequence number, command and arguments. *)
type request = { seq : int; command : string; arguments : json }

module J = Yojson.Safe.Util

exception Not_a_request of string

(* [request_of_string body]: the request of a DAP message. *)
let request_of_string body =
  let json = try Yojson.Safe.from_string body with Yojson.Json_error msg -> raise (Not_a_request msg) in
  match J.member "type" json, J.member "seq" json, J.member "command" json with
  | `String "request", `Int seq, `String command -> { seq; command; arguments = J.member "arguments" json }
  | _ -> raise (Not_a_request body)

(* ---- Reading arguments ------------------------------------------------- *)

(* [field name json]: the field name of an object, `Null when absent or
   when json is not an object. *)
let field name (json : json) = match json with `Assoc l -> Option.value ~default:`Null (List.assoc_opt name l) | _ -> `Null

(* [argument name request]: the argument name, `Null when absent. *)
let argument name (r : request) = field name r.arguments

let string_argument name r = J.to_string_option (argument name r)
let int_argument name r = J.to_int_option (argument name r)
let bool_argument name ~default r = Option.value ~default (J.to_bool_option (argument name r))
let list_argument name r = match argument name r with `List l -> l | _ -> []

(* ---- Writing messages ---------------------------------------------------- *)

(* [response ~seq r ~body]: the success response to r. *)
let response ~seq (r : request) ~body : json =
  `Assoc
    [ ("seq", `Int seq); ("type", `String "response"); ("request_seq", `Int r.seq); ("success", `Bool true);
      ("command", `String r.command); ("body", body) ]

(* [error_response ~seq r message]: the failure response to r. *)
let error_response ~seq (r : request) message : json =
  `Assoc
    [ ("seq", `Int seq); ("type", `String "response"); ("request_seq", `Int r.seq); ("success", `Bool false);
      ("command", `String r.command); ("message", `String message);
      ("body", `Assoc [ ("error", `Assoc [ ("id", `Int 1); ("format", `String message) ]) ]) ]

(* [event ~seq name body]: an event. *)
let event ~seq name body : json = `Assoc [ ("seq", `Int seq); ("type", `String "event"); ("event", `String name); ("body", body) ]

(* [fields l]: the object of the fields whose value is given. *)
let fields l : json = `Assoc (List.filter_map (fun (k, v) -> Option.map (fun v -> (k, v)) v) l)
