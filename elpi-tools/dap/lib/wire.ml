(* The two wire formats of the adapter, read from Unix file descriptors
   without blocking the other one (the main loop selects the descriptor
   that has data, then reads what is there):
   - DAP messages, framed by a header "Content-Length: N\r\n\r\n";
   - lines, the output of elpi-debug. *)

(* ---- Buffered input --------------------------------------------------- *)

(* The bytes read from a descriptor and not consumed yet; [closed] once
   the descriptor reached its end. *)
type input = { fd : Unix.file_descr; pending : Buffer.t; mutable closed : bool }

let input fd = { fd; pending = Buffer.create 4096; closed = false }

(* [fill i]: read what the descriptor has (one read: call it when select
   says it is readable); at the end of the input, [i.closed] is set. *)
let fill i =
  let chunk = Bytes.create 65536 in
  match Unix.read i.fd chunk 0 (Bytes.length chunk) with
  | 0 -> i.closed <- true
  | n -> Buffer.add_subbytes i.pending chunk 0 n
  | exception Unix.Unix_error ((Unix.EINTR | Unix.EAGAIN), _, _) -> ()
  | exception Unix.Unix_error (Unix.ECONNRESET, _, _) -> i.closed <- true

(* [consume i n]: drop the first n pending bytes. *)
let consume i n =
  let rest = Buffer.sub i.pending n (Buffer.length i.pending - n) in
  Buffer.clear i.pending;
  Buffer.add_string i.pending rest

(* [index_of s sub]: the position of the first occurrence of sub in s. *)
let index_of s sub =
  let n = String.length s and m = String.length sub in
  let rec search k = if k + m > n then None else if String.sub s k m = sub then Some k else search (k + 1) in
  search 0

(* ---- Lines -------------------------------------------------------------- *)

(* [next_line i]: the next complete line (without its "\n"), if any; at
   the end of the input, the last line even without its "\n". *)
let next_line i =
  let s = Buffer.contents i.pending in
  match String.index_opt s '\n' with
  | Some k -> consume i (k + 1); Some (String.sub s 0 k)
  | None when i.closed && s <> "" -> consume i (String.length s); Some s
  | None -> None

(* ---- DAP messages --------------------------------------------------------- *)

let header_end = "\r\n\r\n"

(* [content_length header]: the N of "Content-Length: N" in the header. *)
let content_length header =
  let field line =
    match String.index_opt line ':' with
    | Some k when String.lowercase_ascii (String.trim (String.sub line 0 k)) = "content-length" ->
        int_of_string_opt (String.trim (String.sub line (k + 1) (String.length line - k - 1)))
    | _ -> None
  in
  List.find_map field (String.split_on_char '\n' (String.concat "" (String.split_on_char '\r' header)))

exception Bad_header of string

(* [next_message i]: the body of the next complete DAP message, if any. *)
let next_message i =
  let s = Buffer.contents i.pending in
  match index_of s header_end with
  | None -> None
  | Some k -> (
      let header = String.sub s 0 k in
      match content_length header with
      | None -> raise (Bad_header header)
      | Some n ->
          let start = k + String.length header_end in
          if String.length s < start + n then None
          else begin
            consume i (start + n);
            Some (String.sub s start n)
          end)

(* [frame body]: body with its DAP header. *)
let frame body = Printf.sprintf "Content-Length: %d\r\n\r\n%s" (String.length body) body

(* ---- Output ------------------------------------------------------------------ *)

(* [write_all fd s]: write all of s (a write may be partial). *)
let write_all fd s =
  let b = Bytes.of_string s in
  let rec from k =
    if k < Bytes.length b then
      match Unix.write fd b k (Bytes.length b - k) with
      | n -> from (k + n)
      | exception Unix.Unix_error (Unix.EINTR, _, _) -> from k
  in
  from 0
