# Build the command and regenerate the examples (examples/*.md).
ROCQ = rocq c -R . XText -Q ../lexicon Lexicon -Q ../prooftext ProofText

all: Explain.vo paper.vo lemmas.vo inductive.vo thesis.vo stdlib.vo elim_type.vo partial.vo vocab_check.vo selection.vo subproofs.vo multilingual.vo typst_examples.vo implicit_motive.vo

../prooftext/Tactics.vo:
	cd ../prooftext && rocq c -Q . ProofText Tactics.v

Explain.vo: ../prooftext/Tactics.vo Explain.v $(wildcard elpi/*.elpi) $(wildcard ../lexicon/*.elpi) $(wildcard ../prooftext/*.elpi)
	$(ROCQ) Explain.v

paper.vo: paper.v Explain.vo
	$(ROCQ) paper.v

lemmas.vo: lemmas.v Explain.vo
	$(ROCQ) lemmas.v

inductive.vo: inductive.v Explain.vo
	$(ROCQ) inductive.v

thesis.vo: thesis.v Explain.vo
	$(ROCQ) thesis.v

stdlib.vo: stdlib.v Explain.vo
	$(ROCQ) stdlib.v

elim_type.vo: elim_type.v Explain.vo
	$(ROCQ) elim_type.v

partial.vo: partial.v Explain.vo
	$(ROCQ) partial.v

selection.vo: selection.v Explain.vo thesis.vo
	$(ROCQ) selection.v

subproofs.vo: subproofs.v Explain.vo thesis.vo
	$(ROCQ) subproofs.v

vocab_check.vo: vocab_check.v Explain.vo
	$(ROCQ) vocab_check.v

multilingual.vo: multilingual.v paper.vo lemmas.vo inductive.vo thesis.vo
	$(ROCQ) multilingual.v

typst_examples.vo: typst_examples.v paper.vo lemmas.vo inductive.vo
	$(ROCQ) typst_examples.v

implicit_motive.vo: implicit_motive.v Explain.vo lemmas.vo
	$(ROCQ) implicit_motive.v

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux

.PHONY: all clean
