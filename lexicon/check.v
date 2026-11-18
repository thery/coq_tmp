(* Tests of the lexicon's generic predicates: plural categories (CLDR) and
   case folding.  rocq c -Q . Lexicon check.v *)
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

Elpi Command lexicon_check.
Elpi Accumulate File lex_core lex_en lex_fr lex_it lex_de lex_nl lex_ru lex_zh lex_ar lex_ko lex_la.
Elpi Accumulate lp:{{
  pred cats i:string, i:list int, o:list string.
  cats L Ns Cs :- std.map Ns (plural-category L) Cs.
  pred expect i:string, i:list int, i:list string.
  expect L Ns Cs :- cats L Ns Cs0, if (Cs0 = Cs) (coq.say "plural" L ": ok")
    (coq.error "plural" L Ns "gives" Cs0 "expected" Cs).
  main [] :-
    expect "en" [0, 1, 2, 5] ["other", "one", "other", "other"],
    expect "fr" [0, 1, 2, 5] ["one", "one", "other", "other"],
    expect "ru" [1, 2, 5, 11, 12, 21, 22, 25, 101, 111]
      ["one", "few", "many", "many", "many", "one", "few", "many", "one", "many"],
    expect "ar" [0, 1, 2, 3, 10, 11, 99, 100, 102, 103, 111]
      ["zero", "one", "two", "few", "few", "many", "many", "other", "other", "few", "many"],
    expect "zh" [0, 1, 2] ["other", "other", "other"],
    plural "ru" 3 [pr "one" "шаг", pr "few" "шага", pr "many" "шагов"] W, coq.say W,
    lower "ПУСТЬ Über À" Lw, coq.say Lw,
    if (Lw = "пусть über à") (coq.say "lower: ok") (coq.error "lower gives" Lw),
    capitalised "пусть" C1, capitalised "élément" C2, capitalised "`x`" C3,
    if ([C1, C2, C3] = ["Пусть", "Élément", "`x`"]) (coq.say "capitalised: ok")
       (coq.error "capitalised gives" C1 C2 C3).
}}.
Elpi lexicon_check.
