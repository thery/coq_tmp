(* [XText_roles "f.md".]: how cyp's reader (cyp/vernac/elpi/text.elpi)
   reads the formulas of a text written by xtext, with their tags and
   without them.  For each formula whose role is given only by its tag
   (the words before it give another one), prints the line.  Used by
   roles_check.sh on all the texts. *)
From elpi Require Import elpi.
From Lexicon Extra Dependency "lexicon.elpi" as lex_core.
From Lexicon Extra Dependency "lang_en.elpi" as lex_en.
From Lexicon Extra Dependency "lang_fr.elpi" as lex_fr.
From Lexicon Extra Dependency "lang_it.elpi" as lex_it.
From Lexicon Extra Dependency "lang_de.elpi" as lex_de.
From Lexicon Extra Dependency "lang_nl.elpi" as lex_nl.
From Lexicon Extra Dependency "lang_ru.elpi" as lex_ru.
From Lexicon Extra Dependency "lang_zh.elpi" as lex_zh.
From Lexicon Extra Dependency "lang_ar.elpi" as lex_ar.
From Lexicon Extra Dependency "lang_ko.elpi" as lex_ko.
From Lexicon Extra Dependency "lang_la.elpi" as lex_la.
From CypV Extra Dependency "elpi/text.elpi" as cyp_text.

Elpi Command XText_roles.
Elpi Accumulate File lex_core.
Elpi Accumulate File lex_en.
Elpi Accumulate File lex_fr.
Elpi Accumulate File lex_it.
Elpi Accumulate File lex_de.
Elpi Accumulate File lex_nl.
Elpi Accumulate File lex_ru.
Elpi Accumulate File lex_zh.
Elpi Accumulate File lex_ar.
Elpi Accumulate File lex_ko.
Elpi Accumulate File lex_la.
Elpi Accumulate File cyp_text.
Elpi Accumulate lp:{{
  pred lines i:in_stream, o:list string.
  lines I [] :- eof I, !.
  lines I [X | L] :- input_line I X, lines I L.

  % the lines of the text read by cyp: the statement and the list items
  % (the header and the title are left out)
  pred body i:list string, i:int, o:list string.
  body [] _ [].
  body [L | R] N B :- rex.match "^---" L, !, N1 is N + 1, body R N1 B.
  body [L | R] N B :- (N < 2 ; rex.match "^#" L ; L = ""), !, body R N B.
  body [L | R] N [T | B] :- rex.replace "^ *- " "" L T, body R N B.

  pred lang i:list string, o:string.
  lang Ls L :- std.mem Ls X, rex.match "^lang: " X, !, rex.replace "^lang: *" "" X L.
  lang _ "en".

  pred roles i:list element, o:list role.
  roles Es Rs :- std.map-filter Es (e\ r\ sigma F\ e = elt r F) Rs.

  pred role-name i:role, o:string.
  role-name rvar "var".  role-name rhyp "hyp".  role-name rclaim "claim".
  role-name rfact "fact". role-name rback "back".

  % [differs L Out]: Out the description of a formula read differently
  pred differs i:string, o:string.
  differs L Out :-
    justification L _ T,
    pieces T P1, elements P1 rclaim E1, roles E1 R1,
    rex.replace "`{[.][a-z]*}" "`" T T2,
    pieces T2 P2, elements P2 rclaim E2, roles E2 R2,
    not (R1 = R2),
    std.map R1 role-name N1, std.map R2 role-name N2,
    Out is {std.any->string N1} ^ " / words: " ^ {std.any->string N2} ^ " : " ^ L.

  main [str F] :-
    open_in F I, lines I Ls, close_in I,
    lang Ls Lg, body Ls 0 B, std.length B NL,
    ((current-lang Lg :- !) => std.map-filter B differs Ds),
    std.length Ds ND,
    M is "roles: " ^ {std.any->string NL} ^ " lines, " ^ {std.any->string ND} ^
      " with a role given only by a tag: " ^ F,
    coq.say M, std.forall Ds (d\ coq.say {calc ("  " ^ d)}).
}}.
Elpi Export XText_roles.
