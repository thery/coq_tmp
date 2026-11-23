(* The words and the tactic names that the writer puts in a text.
   - The vocabulary (the lexicon, ../lexicon/lang_*.elpi, write-role and
     write-word): each language has a phrase for every use, and the
     phrases of roles are in lower case.
   - The tactics: every name written after *by* or in the header's by
     field (the texts of xtext-tactic, xtext-guard-tactic and xtext-arith-tactic, ExtractText.v) is
     a tactic a proof text may name (../prooftext/tactics.elpi), so that
     cyp can run it. *)
From XText Require Import ExtractText.

Elpi Query ExtractText lp:{{
  switch-values "lang" Langs,
  std.forall Langs (l\ sigma Bad\ vocab-check l Bad,
    if (Bad = []) (coq.say "vocabulary" l ": ok")
       (coq.error "vocabulary" l ":" Bad))
}}.

Elpi Query ExtractText lp:{{
  std.findall (xtext-tactic _ _) Ts, std.findall (xtext-guard-tactic _ _) Gs,
  std.map Ts (t\ n\ sigma L\ t = xtext-tactic L n) Ns1,
  std.map Gs (g\ n\ sigma L\ g = xtext-guard-tactic L n) Ns2,
  std.findall (xtext-arith-tactic _ _) As,
  std.map As (a\ n\ sigma L\ a = xtext-arith-tactic L n) Ns3,
  std.flatten [Ns1, Ns2, Ns3] Names,
  prooftext.unknown-tactics Names Unknown,
  if (Unknown = []) (coq.say "tactic names: ok")
     (coq.error "xtext names tactics that a proof text may not name:" Unknown)
}}.
