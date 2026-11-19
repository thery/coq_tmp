[Back to the README of xtext](../README.md)

# The staged translation (thesis chapters 2 and 3, `elpi/staged.elpi`)

By default (switch `translation`, `staged`), a proof becomes text in the three stages of
Coscoy's thesis, each a predicate on its own data type, so that each can
be read against its figure:

1. **annotation** (3.3.4, Fig. 3.9, `annotate`): each node of the proof
   term gets its *constrained* type Tc (what it proves, partly
   synthesised, 3.3.1) and its *required* type Tr (what is left to prove,
   inherited from the statement, 3.3.2), one clause per rule (Var, Const,
   Abs, App1, App2).  The helpers (synthesis of types, Fig. 3.4; equality
   of type expressions; the required type of the whole proof) are in
   `elpi/type-expressions.elpi`, the weak head normal form (Fig. 3.3) is
   `whnf` (`elpi/printing.elpi`);
2. **contraction** (2.3, and its guarded form, 3.4.2, Fig. 3.11,
   `contract`): nested applications and series of abstractions are
   merged.  The switch `contraction` (variable `XTEXT_CONTRACTION`):
   `none`, `maximal` (every contraction of 2.3) or `guarded` (only the
   contractions that drop a single annotation, so that no conversion step
   disappears); or, with the switch `selection`, the selection of
   type annotations (4.3.1, below), then, with the switch `naming`, the
   subproofs and their names (4.3.2-4.3.3, see ["The subproofs"](subproofs.md));
3. **writing** (2.3.3, Fig. 2.10 for applications; 3.4.1, `write`): a
   conclusion says Tc, then `, that is` Tr when they differ (the thesis's
   "ce qui est équivalent à").

The forms that the thesis treats only in chapter 6 (eliminations,
introductions, rewriting, `fix`) and `let`, `match`, casts are written by
the direct writer; their subproofs come back to the stages.

The direct translation (`XTEXT_TRANSLATION=direct`, texts in
`examples-direct/`) writes a proof in one walk.  Its contraction of
application steps (`applications.elpi`) is not the thesis's: a merge is
kept when a tactic (`xtext-guard-tactic`, `ExtractText.v`) proves the merged
step from its new premises, and the tactic's name becomes the step's
justification.

**Trans_Inv**, Fig. 3.10 of the thesis (doubly annotated, not
contracted), is `examples-staged-none/Trans_Inv.md`: the five double
annotations L1-L5 of the figure are at the same steps,

```markdown
- By h we have `Trans E R`, that is `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`.  [L1]
- By h2 we have `Inv E R y z`, that is `R z y`.                                          [L2]
- By h1 we have `Inv E R x y`, that is `R y x`.                                          [L3]
- By application, we have `R z x`, that is `Inv E R x z`.                                [L4]
- We have proved `forall x0 y z : E, ...`, that is `Trans E (Inv E R)`.                 [L5]
```

with, as in the figure, one sentence per abstraction and per application
(`By application, we have R z y -> R y x -> R z x`) and one for each
element that is not a proof (`The element z belongs to E`).  Fig. 3.12
(maximal contraction) is `examples-staged-maximal/Trans_Inv.md`
(`Applying h to z, y, x, h2 and h1, we have R z x, that is Inv E R x
z`), Fig. 3.13 (guarded contraction) `examples/Trans_Inv.md`.

## The selection of type annotations (thesis 4.3.1, Fig. 4.10)

With the switch `selection` set to `thesis` (variable
`XTEXT_SELECTION=thesis`), the second stage is the thesis's selection
(`select`) instead of the contraction: it decides on the term which type
expressions the text says, by five rewriting rules.  The first three
(redundant type expressions, successive abstractions, successive
applications) are the guarded contraction of Fig. 3.11; the two others
leave out the type of an identifier used as argument or head of an
application: it is the statement of a hypothesis or of a theorem, said
where it was introduced.  Only single annotations are dropped, so every
conversion ("that is") stays.  An argument with no annotation is named in
the sentence of its application ("Applying h2 to h4"); the arguments that
keep one have their own text above it.

`selection.v` checks the selected terms: ABCD is Fig. 4.24,

```
(λA:Prop. λB:Prop. λC:Prop. λD:Prop. λh1:A -> B -> C -> D. λh2:A -> C -> B. λh3:A -> C. λh4:A.
   ((h1 h4 ((h2 h4 ((h3 h4) : C)) : B) ((h3 h4) : C)) : D) : forall A B C D : Prop, ...)
```

and its text (`examples-staged-selection/ABCD.md`), against the guarded
contraction:

```markdown
guarded                                      selection
- By h4 we have `A`.                         - Applying h2 to h4, we have `B`.
- Applying h2, we have `B`.                    - Applying h3 to h4, we have `C`.
  - By h4 we have `A`.                       - Applying h3 to h4, we have `C`.
  - Applying h3 to h4, we have `C`.          - Applying h1 to h4, we have `D`.
- Applying h3 to h4, we have `C`.
- Applying h1, we have `D`.
```

Trans_Inv keeps its three conversions (h, h1, h2) and loses the three
lines "The element z belongs to E": `By application, with z, y and x, we
have R z x, that is Inv E R x z`.

Sizes of the 73 staged texts (the texts in progress left out):

| stage 2 | list items | characters |
|---|---|---|
| contraction none | 1778 | 221981 |
| contraction maximal | 1128 | 118180 |
| contraction guarded | 1164 | 126128 |
| selection | 981 | 112964 |

20 texts differ from the guarded contraction (the others have no
identifier with a single annotation in an application), e.g. ABCD 6 → 4
items, Trans_Inv 9 → 6, half_le 55 → 30, std_Nat_le_trans 187 → 129.

What a reader loses: the statement of each hypothesis or theorem used by
name (`By inj_le we have forall n m : nat, ...` is gone; for a library
theorem the reader must know or look up its statement), the type of each
element named (`The element z belongs to E`), and, in an application
with both named arguments and arguments with a text, the position of the
latter among the arguments.  Type arguments that the direct writer would
infer are named too (`Applying f_equal to nat, nat, S, m0 and IH`): the
staged translation does not leave out inferable arguments (thesis 5.4;
the motive of an elimination, 6.4.1, is left out in both translations).
What a reader keeps: every conversion, every intermediate result that is
not an identifier, and the conclusion of each series of abstractions.
