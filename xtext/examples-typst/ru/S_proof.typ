// The proof text S_proof, written by prooftext (write-typst).
// Its PDF: prooftext/pdf.sh, or typst compile --package-path prooftext/typst.
#import "@local/prooftext:0.1.0": *
#show: proof-text.with(lang: "ru", numbers: false)

#title-block("S_proof", (
  ("require", "From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper."),
  ("lang", "ru"),
  ("by", "tauto | congruence | lia | firstorder | auto"),
))

#statement[#"Пусть "#var($A , B , C : "Prop"$)#". Предположим, что "#hyp($A → B → C$)#" "#name("h", label: "statement:h")#", "#hyp($A → B$)#" "#name("h0", label: "statement:h0")#" и "#hyp($A$)#" "#name("h1", label: "statement:h1")#". Докажем, что "#claim($C$)#"."]

#steps((
  step("1", [#"По "#named("h1", "statement:h1")#" имеем "#claim($A$)#"."], ()),
  step("2", [#"Применяя "#named("h0", "statement:h0")#" к "#named("h1", "statement:h1")#", имеем "#claim($B$)#"."], ()),
  step("3", [#"Применяя "#named("h", "statement:h")#", имеем "#claim($C$)#"."], ()),
))

#legend((("var", "переменная"), ("hyp", "гипотеза"), ("claim", "утверждение"), ("fact", "факт"),))
