(* The writer's vocabulary (the lexicon, ../lexicon/lang_*.elpi, write-role
   and write-word): each language has a phrase for every use, and the
   phrases of roles are in lower case.  How a reader reads them is checked
   by cyp-check/roles_check.sh (optional, with cyp). *)
From XText Require Import Explain.

Elpi Query Explain lp:{{
  std.forall ["en", "fr", "it", "de", "nl", "ru", "zh", "ar", "ko", "la"] (l\ sigma Bad\ vocab-check l Bad,
    if (Bad = []) (coq.say "vocabulary" l ": ok")
       (coq.error "vocabulary" l ":" Bad))
}}.
