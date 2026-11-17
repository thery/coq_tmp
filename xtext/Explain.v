(* The command [Explain foo.]: print the proof of [foo] as text, after the
   basic transducer of "Extracting Text from Proofs" (TLCA 1995).
   [Explain foo to "foo.md".] writes the text to the file foo.md. *)
From Stdlib Require Import Lia.
From elpi Require Import elpi.
From XText Extra Dependency "xtext.elpi" as xtext.

(* The tactics tried on long subproofs (see xtext-tactic below).  Each is
   an Ltac definition (rocq-elpi calls Ltac definitions by name), with a
   time limit. *)
Ltac xtext_tauto := timeout 2 tauto.
Ltac xtext_lia := timeout 2 lia.

Elpi Db xtext.db lp:{{
  % [xtext-tactic Ltac Text]: the Ltac definition Ltac is tried on a long
  % subproof; if it closes it, the step reads "We have P *by Text*".
  % Add yours with: Elpi Accumulate xtext.db lp:{{ xtext-tactic "my_lra" "lra". }}.
  pred xtext-tactic o:string, o:string.
  xtext-tactic "xtext_tauto" "tauto".
  xtext-tactic "xtext_lia" "lia".
  % [xtext-threshold N]: the tactics are tried on a proper subproof whose
  % proof term has at least N nodes.  Change it with
  % Elpi Accumulate xtext.db lp:{{ :before "xtext-threshold" xtext-threshold 50 :- !. }}.
  pred xtext-threshold o:int.
  :name "xtext-threshold"
  xtext-threshold 300.
}}.

Elpi Command Explain.
Elpi Accumulate Db xtext.db.
Elpi Accumulate File xtext.
Elpi Accumulate lp:{{
  main [str N] :- !, explain N T, coq.say T.
  main [str N, str "to", str F] :- !, explain N T,
    open_out F O, output O T, close_out O,
    coq.say "Explain: written" F.
  main _ :- coq.error "usage: Explain name. or Explain name to \"file.md\".".
}}.
Elpi Export Explain.
