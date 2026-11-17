(* The command [Explain foo.]: print the proof of [foo] as text, after the
   basic transducer of "Extracting Text from Proofs" (TLCA 1995).
   [Explain foo to "foo.md".] writes the text to the file foo.md. *)
From elpi Require Import elpi.
From XText Extra Dependency "xtext.elpi" as xtext.

Elpi Command Explain.
Elpi Accumulate File xtext.
Elpi Accumulate lp:{{
  main [str N] :- !, explain N T, coq.say T.
  main [str N, str "to", str F] :- !, explain N T,
    open_out F O, output O T, close_out O,
    coq.say "Explain: written" F.
  main _ :- coq.error "usage: Explain name. or Explain name to \"file.md\".".
}}.
Elpi Export Explain.
