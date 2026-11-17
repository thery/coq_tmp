# Build the command and regenerate the examples (examples/*.md).
ROCQ = rocq c -R . XText

all: Explain.vo paper.vo lemmas.vo inductive.vo thesis.vo stdlib.vo elim_type.vo partial.vo

Explain.vo: Explain.v xtext.elpi
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

# not in all: needs the compiled CORE-MATH exp proof
exp_examples.vo: exp_examples.v Explain.vo
	$(ROCQ) -Q /home/thery/git/libm-coremath-proofs/exp Exp exp_examples.v

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux

.PHONY: all clean
