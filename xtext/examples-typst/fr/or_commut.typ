// The proof text or_commut, written by prooftext (write-typst).
// Its PDF: prooftext/pdf.sh, or typst compile --package-path prooftext/typst.
#import "@local/prooftext:0.1.0": *
#show: proof-text.with(lang: "fr", numbers: false)

#title-block("or_commut", (
  ("require", "From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper."),
  ("lang", "fr"),
  ("by", "tauto | congruence | lia | firstorder | auto"),
))

#statement[#"Soient "#var($A , B : "Prop"$)#". Supposons "#hyp($A ∨ B$)#" "#name("h", label: "statement:h")#". Montrons "#claim($B ∨ A$)#"."]

#steps((
  step("1", [#"Montrons "#formula($B ∨ A$)#" par analyse de cas sur "#by("h", target: "statement:h")#" ("#cited("or", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#", "#by("or_ind", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_ind")#"): Nous avons "#claim($B ∨ A$)#" dans tous les cas."], (
    step("1.1", [#"Cas 1: montrons "#claim($A → B ∨ A$)#"."], (
      step("1.1.1", [#"Supposons "#hyp($A$)#" "#name("i", label: "1.1.1:i")#". Par définition de "#cited("or", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#" ("#by("or_intror", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_intror")#"), à partir de "#by("i", target: "1.1.1:i")#" nous en déduisons "#claim($B ∨ A$)#"."], ()),
    )),
    step("1.2", [#"Cas 2: montrons "#claim($B → B ∨ A$)#"."], (
      step("1.2.1", [#"Supposons "#hyp($B$)#" "#name("j", label: "1.2.1:j")#". Par définition de "#cited("or", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#" ("#by("or_introl", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_introl")#"), à partir de "#by("j", target: "1.2.1:j")#" nous en déduisons "#claim($B ∨ A$)#"."], ()),
    )),
  )),
))

#legend((("var", "variable"), ("hyp", "hypothèse"), ("claim", "affirmation"), ("fact", "fait"), ("by", "justification"),))
