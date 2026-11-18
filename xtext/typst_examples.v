(* Texts in Typst, for their PDFs: Explain foo to "foo.typ" writes the
   document of the proof with prooftext's Typst writer (write-typst) in
   place of the Markdown one.  Five English texts and one per other script
   (French, Arabic from right to left, Chinese, Russian, Korean), written
   to examples-typst/.  ../prooftext/typst/check.sh compiles them to PDF,
   and checks that each is the Typst source that prooftext's reader gives
   from the Markdown text in examples/ (the same document either way). *)
From XText Require Import Explain paper lemmas inductive.
Explain and_swap to "examples-typst/and_swap.typ".
Explain or_commut to "examples-typst/or_commut.typ".
Explain add_0_r' to "examples-typst/add_0_r.typ".
Explain plus_n_Sm' to "examples-typst/plus_n_Sm.typ".
Explain le_n_S' to "examples-typst/le_n_S.typ".
Explain or_commut to "examples-typst/fr/or_commut.typ" in "fr".
Explain or_commut to "examples-typst/ar/or_commut.typ" in "ar".
Explain or_commut to "examples-typst/zh/or_commut.typ" in "zh".
Explain S_proof to "examples-typst/ru/S_proof.typ" in "ru".
Explain or_commut to "examples-typst/ko/or_commut.typ" in "ko".
