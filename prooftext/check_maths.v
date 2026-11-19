(* Tests of the printer of formulas as mathematics (maths.elpi and its
   table, maths-table.elpi): each formula, elaborated under declarations,
   gives the expected Typst maths code.  Each code is also written, one
   formula per paragraph, to check_maths.typ in the current directory, so
   that typst/check.sh compiles them to a PDF and to HTML.
   rocq c -Q ../lexicon Lexicon -Q . ProofText check_maths.v *)
From elpi Require Import elpi.
From Stdlib Require Import Reals ZArith List.
From ProofText Extra Dependency "maths-table.elpi" as pt_maths_table.
From ProofText Extra Dependency "maths.elpi" as pt_maths.
From ProofText Extra Dependency "maths-typst.elpi" as pt_maths_typst.
From ProofText Extra Dependency "links.elpi" as pt_links.
From ProofText Extra Dependency "typst.elpi" as pt_typst.
From Lexicon Extra Dependency "lexicon.elpi" as lex_core.
From ProofText Extra Dependency "header.elpi" as pt_header.
From ProofText Extra Dependency "document.elpi" as pt_document.
From ProofText Extra Dependency "formulas.elpi" as pt_formulas.
From ProofText Extra Dependency "tree.elpi" as pt_tree.
From ProofText Extra Dependency "nodes.elpi" as pt_nodes.
From ProofText Extra Dependency "checked.elpi" as pt_checked.

Elpi Command prooftext_check_maths.
Elpi Accumulate File lex_core pt_header pt_document pt_formulas pt_tree pt_nodes pt_checked
  pt_maths_table pt_maths pt_maths_typst pt_links pt_typst.
Elpi Accumulate lp:{{
  % [formula Scope Declarations F Wanted]: F gives the code Wanted
  pred formula i:string, i:list string, i:string, i:string.
  formula Scope Ds F Wanted :-
    (prooftext.formula-maths Scope Ds F E, !, prooftext.maths-typst E Got ; Got = "(does not elaborate)"),
    if (Got = Wanted) (coq.say "ok  " F "  ⟶  " Got, typst-paragraph Got)
       (coq.error "FAIL" F ": got" Got "wanted" Wanted).

  % [declaration Scope Declarations D Wanted]: the declaration D gives Wanted
  pred declaration i:string, i:list string, i:string, i:string.
  declaration Scope Ds D Wanted :-
    (prooftext.declaration-maths Scope Ds D E, !, prooftext.maths-typst E Got ; Got = "(not a declaration)"),
    if (Got = Wanted) (coq.say "ok  " D "  ⟶  " Got, typst-paragraph Got)
       (coq.error "FAIL" D ": got" Got "wanted" Wanted).

  % [untagged F Wanted]: a formula F without a class is a declaration
  % (Wanted = tt) or a formula (Wanted = ff)
  pred untagged i:string, i:bool.
  untagged F Wanted :-
    (prooftext.is-declaration "" F, !, Got = tt ; Got = ff),
    if (Got = Wanted) (coq.say "ok  " F "  ⟶  declaration:" Got)
       (coq.error "FAIL" F ": declaration" Got "wanted" Wanted).

  % [typst-paragraph Code]: the maths Code, a paragraph of check_maths.typ
  pred typst-paragraph i:string.
  typst-paragraph "(does not elaborate)" :- !.
  typst-paragraph Code :-
    open_append "check_maths.typ" O, output O {calc ("$" ^ Code ^ "$\n\n")}, close_out O.

  main [] :-
    open_out "check_maths.typ" O, close_out O,
    R = ["a b c x y : R"], N = ["n m : nat"], Z = ["a b : Z"], P = ["A B C : Prop"],
    % precedence and associativity
    formula "R_scope" R "a - (b - c)" "a - \\(b - c\\)",
    formula "R_scope" R "(a - b) - c" "a - b - c",
    formula "R_scope" R "(a + b) * c" "\\(a + b\\) ⋅ c",
    formula "R_scope" R "a + b * c" "a + b ⋅ c",
    formula "R_scope" R "a / (b / c)" "frac(a, frac(b, c))",
    formula "R_scope" R "(a + b) / c * x" "frac(a + b, c) ⋅ x",
    formula "R_scope" R "- (x ^ 2)" "- x^(2)",
    formula "R_scope" R "(- x) ^ 2" "\\(- x\\)^(2)",
    formula "R_scope" R "a - - b" "a - \\(- b\\)",
    formula "R_scope" R "(a + b) ^ (2 + 1)" "\\(a + b\\)^(2 + 1)",
    formula "R_scope" R "(a / b) ^ 2" "(frac(a, b))^(2)",
    formula "R_scope" R "/ x" "frac(1, x)",
    formula "R_scope" R "Rabs (x - y) <= sqrt (x ^ 2 + y ^ 2)" "lr(| x - y |) ≤ sqrt(x^(2) + y^(2))",
    formula "R_scope" R "sqrt x ^ 2 = x" "\\(sqrt(x)\\)^(2) = x",
    formula "R_scope" R "Rsqr (a + b) = a² + 2 * a * b + b²" "\\(a + b\\)^(2) = a^(2) + 2 ⋅ a ⋅ b + b^(2)",
    formula "R_scope" R "exp (ln x) = x" "\"exp\"\\(\"ln\"\\(x\\)\\) = x",
    formula "R_scope" R "Rpower x y > 0" "x^(y) > 0",
    formula "R_scope" N "INR n + 1 = INR (n + 1)" "n + 1 = n + 1",
    formula "R_scope" R "x <> -1" "x ≠ -1",
    formula "R_scope" R "x + -1 = 0" "x + \\(-1\\) = 0",
    % logic: implications, quantifiers, negation
    formula "" P "A -> B -> C" "A → B → C",
    formula "" P "(A -> B) -> C" "\\(A → B\\) → C",
    formula "" P "A /\\ B \\/ C" "A ∧ B ∨ C",
    formula "" P "A /\\ (B \\/ C)" "A ∧ \\(B ∨ C\\)",
    formula "" P "~ (A /\\ B) <-> (~ A \\/ ~ B)" "¬ \\(A ∧ B\\) ↔ ¬ A ∨ ¬ B",
    formula "" P "~ ~ A" "¬ ¬ A",
    formula "" [] "forall n : nat, n + 0 = n" "∀ n ∈ ℕ , n + 0 = n",
    formula "" [] "forall n m : nat, n <= m -> exists k, m = n + k"
      "∀ n , m ∈ ℕ , n ≤ m → \\(∃ k ∈ ℕ , m = n + k\\)",
    formula "" [] "forall x : R, exists y : nat, forall z : R, (x < z)%R"
      "∀ x ∈ ℝ , ∃ y ∈ ℕ , ∀ z ∈ ℝ , x < z",
    formula "" [] "forall P : nat -> Prop, P 0 -> forall n, P n"
      "∀ P : ℕ → \"Prop\" , P\\(0\\) → \\(∀ n ∈ ℕ , P\\(n\\)\\)",
    formula "" [] "(forall A : Prop, A) -> False" "\\(∀ A : \"Prop\" , A\\) → ⊥",
    % integers, naturals, lists, booleans, functions without entries
    formula "Z_scope" Z "0 < a < b" "0 < a < b",
    formula "Z_scope" Z "0 < a /\\ b < a" "0 < a ∧ b < a",
    formula "Z_scope" Z "a <= b < a + 1 /\\ a = b" "a ≤ b < a + 1 ∧ a = b",
    formula "Z_scope" Z "a * a < b * b" "a ⋅ a < b ⋅ b",
    formula "Z_scope" Z "(a mod b + Z.abs a) / 2 = - a" "\\(a class(\"binary\", \"mod\") b + lr(| a |)\\) class(\"binary\", \"div\") 2 = - a",
    formula "Z_scope" Z "a ^ 2 >= 0" "a^(2) ≥ 0",
    formula "" N "S n <= S m" "\"S\"\\(n\\) ≤ \"S\"\\(m\\)",
    formula "" N "n0 = 3" "(does not elaborate)",
    formula "" ["n0 n' : nat"] "n0 = n'" "n_(0) = n'",
    formula "" ["l m : list nat", "x : nat"] "length (x :: l ++ m) = S (length l + length m)"
      "\"length\"\\(x class(\"binary\", \"::\") l class(\"binary\", \"++\") m\\) = \"S\"\\(\"length\"\\(l\\) + \"length\"\\(m\\)\\)",
    formula "" ["l : list nat", "x : nat"] "In x l \\/ l = nil" "x ∈ l ∨ l = \"[]\"",
    formula "bool_scope" ["b c : bool"] "negb (b && c) = negb b || negb c" "\\(¬ \\(b ∧ c\\)\\) = \\(¬ b ∨ ¬ c\\)",
    formula "" ["f : nat -> nat", "IH : Prop"] "f (f 2) = 2 /\\ IH" "f\\(f\\(2\\)\\) = 2 ∧ italic(\"IH\")",
    formula "" ["l : list nat"] "map (fun x => x + 1) l = l" "\"map\"\\(\\(x ↦ x + 1\\), l\\) = l",
    formula "" N "match n with 0 => m | S k => k end = m"
      "\\(\"match n with | 0 => m | S k => k end\"\\) = m",
    % declarations (Let)
    declaration "" [] "a b : Z" "a , b ∈ ℤ",
    declaration "" [] "A B : Prop" "A , B : \"Prop\"",
    declaration "" [] "n : nat" "n ∈ ℕ",
    declaration "" [] "x y : R" "x , y ∈ ℝ",
    declaration "R_scope" ["x : R"] "y := x * x" "y ≔ x ⋅ x",
    declaration "" [] "f : nat -> nat" "f : ℕ → ℕ",
    declaration "" [] "p : nat * nat" "p ∈ ℕ × ℕ",
    % formulas without a class: declarations, or formulas with binders
    untagged "n : nat" tt,
    untagged "a b : Z" tt,
    untagged "y := x * x" tt,
    untagged "forall z : nat, z = z" ff,
    untagged "fun f : nat -> nat => f 0" ff,
    untagged "exists x : nat, x = 0" ff,
    untagged "n + 0 = n" ff,
    formula "" ["A : Type", "l : list A"] "fun f : list A -> list A => f l" "f ↦ f\\(l\\)".
}}.
Elpi prooftext_check_maths.
