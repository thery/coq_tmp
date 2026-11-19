[Back to the README of xtext](../README.md)

# The subproofs (thesis 4.3.2-4.3.3, `elpi/subproofs.elpi`)

With the switch `naming` set to `all` (variable `XTEXT_NAMING=all`) and
the selection (`XTEXT_SELECTION=thesis`; with another selection `naming`
is an error), the selected term goes through the two next steps of the
thesis before it is written:

1. **translatable occurrences** (4.3.2, Fig. 4.12, `translatable`): the
   proofs the text translates are the root, the term under a type
   annotation, the body of an abstraction, the function of an
   application, and an argument whose function has the type T ⇒ T' (T a
   proposition, T' not depending on the argument).  A proof argument that
   a type depends on is written as a term ("The element `g b` belongs to
   `A`"): naming it would make the term ill-typed.  Likewise (Fig. 4.13)
   a binder of a proposition the rest of the type depends on is
   introduced as a variable (`Let b : B`), not as a hypothesis;
2. **intermediate results** (4.3.3, Fig. 4.14, `name-subproofs`): each
   translatable subproof that is the function or an argument of an
   application and keeps a type expression becomes a local definition,
   `let P1 : C = (h3 h4) in ...`, its own results first (postfix order),
   so that the proof reads as a list of facts.  The results under a named
   abstraction stay under it and are numbered after its name (P1.1); so
   are those of a case analysis or an induction inside an application.
   With `shared` (`XTEXT_NAMING=shared`, Fig. 4.17) a subproof whose type
   a result in scope already proves is not proved again: that result is
   used.

A named result is a step whose claim is followed by its name, the way a
hypothesis is named, and the steps after it use the name.  ABCD
(`examples-staged-naming/ABCD.md`, Fig. 4.30: "Preuve P1 : montrons C.
Nous appliquons h3 à h4. Fin de P1. ..."):

```markdown
- Applying *h3*{.just} to *h4*{.just}, we have `C`{.claim} (P1).
- Applying *h2*{.just} to *h4*{.just} and *P1*{.just}, we have `B`{.claim} (P2).
- Applying *h3*{.just} to *h4*{.just}, we have `C`{.claim} (P3).
- Applying *h1*{.just} to *h4*{.just}, *P2*{.just} and *P3*{.just}, we have `D`{.claim}.
```

and with `shared` (`examples-staged-shared/ABCD.md`) the third step goes
and the last one says "P2 and P1".  `subproofs.v` checks the terms of
Fig. 4.27 and 4.17 (exactly the thesis's), the French text of Fig. 4.30
("En appliquant h2 à h4 et P1, nous avons `B` (P2)."), and the cases above
(a dependent argument, a named abstraction, a case analysis inside an
application).  An argument that keeps a text is named, so its place among
the arguments, which the selection alone loses, is kept.  A conversion
is named too: in Trans_Inv, `By h we have Trans E R, that is forall x0
y0 z0 : E, ... (P1)`, then `Applying P1 to z, y, x, P2 and P3, we have R
z x, that is Inv E R x z`.

18 of the 73 staged texts change (the others have no subproof that keeps
a type in an application); the number of list items stays 981 (each
named result was already a step of its own: it moves before the step
that uses it), 112682 characters against 112964; `shared` makes 4 texts
shorter (968 items).  cyp reads the 18 texts with names as it reads them without:
the same steps proved, not proved and not checked, text by text
(2026-11-18; the names are read as the names of claims, and each step is
proved from the claims before it, as before); the 4 texts of `shared`
lose only the steps they drop (the same steps not proved).  The departures from the thesis (the rules of
Fig. 4.14 for applications of several arguments, Dewey numbers only
under a named abstraction, the text of a named result) are listed in
[THESIS.md](../THESIS.md).

An earlier version computed the same double annotation in one pass, as
hooks in the direct writer (switch `xtext-annotation`, texts
`examples-double/`); it was removed in favour of the stages, which give
the same annotations (it is in the history, commit 56a84ef).
