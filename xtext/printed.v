(* The two forms of a text.  [ExtractText foo.] prints plain text: no
   header, no title, no backticks, classes or emphasis; the list of the
   steps stays.  [#[tags] ExtractText foo.] prints the format of proof
   texts, as the files that [ExtractText foo to "foo.md".] writes (the
   form cyp, the Typst writer and the gallery read). *)
From XText Require Import ExtractText lemmas thesis.

(* both forms, in English and in another language *)
ExtractText add_0_r'.
#[tags] ExtractText add_0_r'.
ExtractText add_0_r' in "fr".
#[tags] ExtractText add_0_r' in "fr".
(* an attribute the command does not know is an error *)
Fail #[colour] ExtractText add_0_r'.

Elpi Query ExtractText lp:{{
  % the plain text of add_0_r', in English
  sigma D Plain Expected Tagged File\
  with-switches (extract-text "add_0_r'" D),
  prooftext.write-document-as prooftext.untagged D Plain,
  Expected = {std.string.concat "\n" [
    "Let n : nat. We prove n + 0 = n.",
    "",
    "- We prove n + 0 = n by induction on n (nat, nat_ind):",
    "  - Case 1 (base): we prove 0 = 0.",
    "    - By definition of eq (eq_refl), we have 0 = 0.",
    "  - Case 2 (inductive): we prove forall m : nat, m + 0 = m -> S m + 0 = S m.",
    "    - Let us choose arbitrarily m : nat; assume by induction hypothesis m + 0 = m (IH).",
    "      - By definition of eq (eq_refl), we have S m = S m.",
    "      - By IH we have m + 0 = m.",
    "",
    "      Rewriting with m + 0 = m from right to left (eq_ind_r), we get S (m + 0) = S m.",
    "",
    "  These cases being exhaustive, we deduce n + 0 = n.",
    ""]},
  if (Plain = Expected) (coq.say "plain text: ok")
     (coq.error "plain text:" Plain "and not" Expected),
  % the tagged form is the form of the files
  prooftext.write-document-as prooftext.tagged D Tagged,
  prooftext.write-document D File,
  if (Tagged = File) (coq.say "tagged text = the text of a file: ok")
     (coq.error "the tagged text is not the text of a file")
}}.

Elpi Query ExtractText lp:{{
  % in every language: the plain text of Trans_Inv has no markup (no line
  % with a backtick, a star, a class, a header or a title) and the lines
  % of the tagged text, but its header and its title
  sigma Langs\ switch-values "lang" Langs,
  std.forall Langs (l\ sigma D Fields Header Plain Tagged PLines TLines NP NT NH\
    with-switches (with-switch "lang" "the test" l (extract-text "Trans_Inv" D)),
    prooftext.write-document-as prooftext.untagged D Plain,
    prooftext.write-document-as prooftext.tagged D Tagged,
    rex.split "\n" Plain PLines, rex.split "\n" Tagged TLines,
    (if (std.exists PLines (x\ rex.match "^\\(.*[`*]\\|.*{[.]\\|---\\|# \\)" x))
        (coq.error "plain text in" l "has markup:" Plain) true),
    std.length PLines NP, std.length TLines NT,
    D = prooftext.document Fields _ _ _ _, prooftext.header-lines Fields Header,
    std.length Header NH,
    (if (NT is NP + NH + 3) true
        (coq.error "plain text in" l ": not the lines of the tagged text")),
    coq.say "plain text in" l ": ok")
}}.
