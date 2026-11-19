# lexicon: the words of proofs, per language

The data shared by a reader of proofs written in natural language (cyp)
and a writer of such proofs (xtext): what a formula is in a step (its
*role*), and, for each language, the phrases that give a role, the
writer's phrases, the capital letters, and the plural rule.  Pure data,
with the few generic predicates over it; no reading or writing logic.

Load with `-Q lexicon Lexicon` and, in Rocq-Elpi,

```coq
From Lexicon Extra Dependency "lexicon.elpi" as lex_core.
From Lexicon Extra Dependency "lang_en.elpi" as lex_en.   (* and the others *)
Elpi Accumulate File lex_core.      (* first: the declarations *)
Elpi Accumulate File lex_en.        (* then the tables, in any order *)
```

## lexicon.elpi

- roles: `rvar` (a variable or a definition introduced), `rhyp` (a
  hypothesis), `rclaim` (a claim, proved by the step), `rfact` (a fact
  used, a mention), `rback` (a claim that replaces the goal);
- `phrase Lang Phrase Role`: a phrase (in lower case) that gives its role
  to a formula; `phrase-after Lang Phrase`: the phrase stands after the
  formula (default: before);
- `write-role Lang Use Phrase Role` and `write-word Lang Use Words`: the
  phrases of a writer, by their use (the same uses in every language); a
  `write-role` phrase is also a `phrase` (one clause); the uses
  `legend-var`, `legend-hyp`, `legend-claim`, `legend-fact`, `legend-just`
  (the justifications) and `legend-ok`, `legend-ko`, `legend-todo`, `legend-none` are the words of
  the legend of a PDF or a web page of a proof text (the names of the
  roles and of cyp's statuses, [prooftext](../prooftext/README.md#the-legend));
- writing systems: `capital Lang Upper Lower` (case folding: `lower S L`
  uses the capitals of all the languages loaded, `capitalised S C` puts
  the first letter of `S` in capitals), `clitic Lang Prefix`
  (a prefix glued to the next word), `punctuation Lang P` (punctuation
  other than ASCII), `unspaced Lang` (no spaces between words);
- plural: `plural-category Lang N Cat` (the categories of the Unicode
  CLDR plural rules for integers: zero, one, two, few, many, other) and
  `plural Lang N Forms W` (the form of a word for a count, from its forms
  by category).

## The tables

One file per language, `lang_<code>.elpi`; the phrases of each are listed
below so that a speaker can review them.

Languages: English (en), French (fr), Italian (it), German (de), Dutch
(nl), Russian (ru), Chinese (zh, unspaced), Arabic (ar, clitics و ف),
Korean (ko, phrases after the formula), Latin (la, phrases before the
formula only).  British English needs no table of its own: no phrase
differs.  The phrases follow the usual style of mathematical texts in
each language (textbook phrasing such as "Sei ...", "Пусть ...", "设 ...",
"ليكن ...", "Sit ..."); none of them was checked by a native speaker.

The tables below are made from the files by `sh tables.sh` (phrases that
give a role are in lower case, as they are matched; the writer
capitalises the start of a sentence).  "side": where the phrase stands
with respect to the formula it governs; "(none)": a word that gives no
role.

Tests: `rocq c -Q . Lexicon check.v` (plural categories of en, fr, ru, ar,
zh on sample counts; case folding).

## What a reader and a writer need to load

In this order: `lexicon.elpi`, then the `lang_<code>.elpi` files (any
order), then the reader's or the writer's own files.  For cyp's commands
(cyp/vernac/Cyp.v): `lexicon.elpi`, `lang_en.elpi`, `lang_fr.elpi`,
`lang_it.elpi`, `lang_de.elpi`, `lang_nl.elpi`, `lang_ru.elpi`,
`lang_zh.elpi`, `lang_ar.elpi`, `lang_ko.elpi`, `lang_la.elpi`, before
`elpi/text.elpi` (which uses the type `role`).

### Arabic (ar)

| use | phrase | role | side |
|---|---|---|---|
| let | ليكن | var | before |
| let-plural | لتكن | var | before |
| consider | لنأخذ عنصرا اختياريا | var | before |
| choose | لنختر اختياريا | var | before |
| assume | لنفرض أن | hyp | before |
| we-prove | سنثبت أن | claim | before |
| prove | يجب إثبات أن | claim | before |
| proved | لقد أثبتنا أن | claim | before |
| have | لدينا | claim | before |
| thus-have | وبالتالي لدينا | claim | before |
| get | نحصل على | claim | before |
| particular | بشكل خاص | claim | before |
| deduce | نستنتج أن | claim | before |
| can-deduce | يمكننا أن نستنتج أن | claim | before |
| so | إذن | claim | before |
| from | من | fact | before |
| since | بما أن | fact | before |
| using | باستخدام | fact | before |
| that-is | أي | fact | before |
| witness | مع الشاهد | fact | before |
| by-induction-on | بالاستقراء على | fact | before |
| by-cases-on | بدراسة الحالات على | fact | before |
| generalise | نعممها إلى | fact | before |
| recursion | بالتكرار على | fact | before |
| rewriting | بإعادة الكتابة باستخدام | fact | before |
| the-term | الحد | fact | before |
| and | و | (none) | before |
| by | حسب | (none) | before |
| arbitrary | اختياري | (none) | before |
| ih | حسب فرضية الاستقراء | (none) | before |
| recursive-call | الاستدعاء التكراري | (none) | before |
| definition | حسب تعريف | (none) | before |
| case | الحالة | (none) | before |
| base | الأساس | (none) | before |
| inductive | الاستقرائية | (none) | before |
| contradiction | بالتناقض | (none) | before |
| back | بالعودة إلى تعريف | (none) | before |
| in | في | (none) | before |
| by-induction | بالاستقراء | (none) | before |
| by-cases | بدراسة الحالات | (none) | before |
| on | على | (none) | before |
| all-cases | في جميع الحالات | (none) | before |
| no-element | لا يوجد عنصر من | (none) | before |
| to-prove | لإثبات | (none) | before |
| exhaustive | هذه الحالات شاملة | (none) | before |
| fix | fix | (none) | before |
| argument | الوسيط | (none) | before |
| left-right | من اليسار إلى اليمين | (none) | before |
| right-left | من اليمين إلى اليسار | (none) | before |
| not-translated | غير مترجم | (none) | before |

Read only: إذا كان (hyp); إن (claim); يكفي أن نثبت أن (back); هذا يكافئ (back).

Writing system: `clitic "ar" "و".  clitic "ar" "ف". punctuation "ar" "،".  punctuation "ar" "؛".  punctuation "ar" "؟". `

### German (de)

| use | phrase | role | side |
|---|---|---|---|
| let | sei | var | before |
| let-plural | seien | var | before |
| consider | sei beliebig | var | before |
| choose | seien beliebig | var | before |
| assume | angenommen | hyp | before |
| we-prove | wir zeigen | claim | before |
| prove | zu zeigen | claim | before |
| proved | wir haben gezeigt | claim | before |
| have | es gilt | claim | before |
| thus-have | also gilt | claim | before |
| get | wir erhalten | claim | before |
| particular | insbesondere | claim | before |
| deduce | daraus folgt | claim | before |
| can-deduce | können wir folgern | claim | before |
| so | also | claim | before |
| from | aus | fact | before |
| since | da | fact | before |
| using | mit | fact | before |
| that-is | das heißt | fact | before |
| generalise | verallgemeinern wir es zu | fact | before |
| witness | mit dem Zeugen | (none) | before |
| by-induction-on | durch Induktion über | (none) | before |
| by-cases-on | durch Fallunterscheidung über | (none) | before |
| recursion | durch Rekursion über | (none) | before |
| rewriting | durch Umschreiben mit | (none) | before |
| the-term | der Term | (none) | before |
| and | und | (none) | before |
| by | nach | (none) | before |
| arbitrary | beliebig ist | (none) | before |
| ih | nach Induktionsvoraussetzung | (none) | before |
| recursive-call | dem rekursiven Aufruf | (none) | before |
| definition | nach Definition von | (none) | before |
| case | Fall | (none) | before |
| base | Anfang | (none) | before |
| inductive | Schritt | (none) | before |
| contradiction | durch Widerspruch | (none) | before |
| back | zurück zur Definition von | (none) | before |
| in | in | (none) | before |
| by-induction | durch Induktion | (none) | before |
| by-cases | durch Fallunterscheidung | (none) | before |
| on | über | (none) | before |
| all-cases | in allen Fällen | (none) | before |
| no-element | es gibt kein Element von | (none) | before |
| to-prove | um zu zeigen | (none) | before |
| exhaustive | da diese Fälle vollständig sind | (none) | before |
| fix | fix | (none) | before |
| argument | Argument | (none) | before |
| left-right | von links nach rechts | (none) | before |
| right-left | von rechts nach links | (none) | before |
| not-translated | nicht übersetzt | (none) | before |

Read only: sei (var); seien (var); wenn (hyp); falls (hyp); dann (claim); folgt (claim); wir haben (claim); es genügt zu zeigen (back); es reicht zu zeigen (back); das ist gleichbedeutend mit (back).

### English (en)

| use | phrase | role | side |
|---|---|---|---|
| let | let | var | before |
| let-plural | let | var | before |
| consider | let us consider an arbitrary | var | before |
| choose | let us choose arbitrarily | var | before |
| assume | assume | hyp | before |
| we-prove | we prove | claim | before |
| prove | prove | claim | before |
| proved | we have proved | claim | before |
| have | we have | claim | before |
| thus-have | thus we have | claim | before |
| get | we get | claim | before |
| particular | in particular | claim | before |
| deduce | we deduce | claim | before |
| can-deduce | we can deduce | claim | before |
| so | so | claim | before |
| from | from | fact | before |
| since | since | fact | before |
| using | using | fact | before |
| that-is | that is | fact | before |
| witness | with witness | fact | before |
| by-induction-on | by induction on | fact | before |
| by-cases-on | by case analysis on | fact | before |
| generalise | we generalise it to | fact | before |
| recursion | by recursion on | fact | before |
| rewriting | rewriting with | fact | before |
| the-term | the term | fact | before |
| and | and | (none) | before |
| by | by | (none) | before |
| arbitrary | is arbitrary | (none) | before |
| ih | by induction hypothesis | (none) | before |
| recursive-call | the recursive call | (none) | before |
| definition | by definition of | (none) | before |
| case | case | (none) | before |
| base | base | (none) | before |
| inductive | inductive | (none) | before |
| contradiction | by contradiction | (none) | before |
| back | going back to the definition of | (none) | before |
| in | in | (none) | before |
| by-induction | by induction | (none) | before |
| by-cases | by case analysis | (none) | before |
| on | on | (none) | before |
| all-cases | in all cases | (none) | before |
| no-element | there is no element of | (none) | before |
| to-prove | to prove | (none) | before |
| exhaustive | these cases being exhaustive | (none) | before |
| fix | fix | (none) | before |
| argument | argument | (none) | before |
| left-right | from left to right | (none) | before |
| right-left | from right to left | (none) | before |
| not-translated | not translated | (none) | before |

Read only: let (var); if (hyp); assume (hyp); suppose (hyp); from (fact); using (fact); since (fact); because (fact); for (fact); then (claim); show (claim); prove (claim); have (claim); get (claim); thus (claim); hence (claim); so (claim); obtain (claim); deduce (claim); is (claim); that is (fact); suffices (back); enough (back); equivalent to prove (back); written as (back); amounts to (back); reduces to (back); suffices to prove (back); suffices to show (back); enough to prove (back); enough to show (back); suffices to check (back); enough to check (back).

### French (fr)

| use | phrase | role | side |
|---|---|---|---|
| let | soit | var | before |
| let-plural | soient | var | before |
| consider | considérons un élément arbitraire | var | before |
| choose | choisissons arbitrairement | var | before |
| assume | supposons | hyp | before |
| we-prove | montrons | claim | before |
| prove | prouvez | claim | before |
| proved | nous avons prouvé | claim | before |
| have | nous avons | claim | before |
| thus-have | ainsi nous avons | claim | before |
| get | nous obtenons | claim | before |
| particular | en particulier | claim | before |
| deduce | nous en déduisons | claim | before |
| can-deduce | nous pouvons déduire | claim | before |
| so | donc | claim | before |
| from | à partir de | fact | before |
| since | puisque | fact | before |
| using | en utilisant | fact | before |
| that-is | c'est-à-dire | fact | before |
| witness | avec le témoin | fact | before |
| by-induction-on | par récurrence sur | fact | before |
| by-cases-on | par analyse de cas sur | fact | before |
| generalise | nous le généralisons en | fact | before |
| recursion | par récursion sur | fact | before |
| rewriting | en réécrivant avec | fact | before |
| the-term | le terme | fact | before |
| and | et | (none) | before |
| by | par | (none) | before |
| arbitrary | est arbitraire | (none) | before |
| ih | par hypothèse de récurrence | (none) | before |
| recursive-call | l'appel récursif | (none) | before |
| definition | par définition de | (none) | before |
| case | cas | (none) | before |
| base | base | (none) | before |
| inductive | inductif | (none) | before |
| contradiction | par contradiction | (none) | before |
| back | en revenant à la définition de | (none) | before |
| in | dans | (none) | before |
| by-induction | par récurrence | (none) | before |
| by-cases | par analyse de cas | (none) | before |
| on | sur | (none) | before |
| all-cases | dans tous les cas | (none) | before |
| no-element | il n'y a pas d'élément de | (none) | before |
| to-prove | pour montrer | (none) | before |
| exhaustive | ces cas étant exhaustifs | (none) | before |
| fix | fix | (none) | before |
| argument | argument | (none) | before |
| left-right | de gauche à droite | (none) | before |
| right-left | de droite à gauche | (none) | before |
| not-translated | non traduit | (none) | before |

Read only: soit (var); soient (var); considérons (var); si (hyp); supposons (hyp); posons par hypothèse (hyp); à partir de (fact); en utilisant (fact); puisque (fact); d'après (fact); grâce à (fact); ce qui est équivalent à (fact); alors (claim); montrons (claim); prouvons (claim); nous avons (claim); on a (claim); donc (claim); ainsi (claim); d'où (claim); nous en déduisons (claim); nous déduisons (claim); nous obtenons (claim); on obtient (claim); il suffit (back); revient à (back); se réduit à (back); équivaut à montrer (back); il suffit de montrer (back); il suffit de prouver (back).

### Italian (it)

| use | phrase | role | side |
|---|---|---|---|
| let | sia | var | before |
| let-plural | siano | var | before |
| consider | consideriamo un elemento arbitrario | var | before |
| choose | scegliamo arbitrariamente | var | before |
| assume | supponiamo | hyp | before |
| we-prove | dimostriamo | claim | before |
| prove | resta da dimostrare | claim | before |
| proved | abbiamo dimostrato | claim | before |
| have | abbiamo | claim | before |
| thus-have | quindi abbiamo | claim | before |
| get | otteniamo | claim | before |
| particular | in particolare | claim | before |
| deduce | ne deduciamo | claim | before |
| can-deduce | possiamo dedurre | claim | before |
| so | dunque | claim | before |
| from | da | fact | before |
| since | poiché | fact | before |
| using | usando | fact | before |
| that-is | cioè | fact | before |
| witness | con testimone | fact | before |
| by-induction-on | per induzione su | fact | before |
| by-cases-on | per casi su | fact | before |
| generalise | lo generalizziamo in | fact | before |
| recursion | per ricorsione su | fact | before |
| rewriting | riscrivendo con | fact | before |
| the-term | il termine | fact | before |
| and | e | (none) | before |
| by | per | (none) | before |
| arbitrary | è arbitrario | (none) | before |
| ih | per ipotesi di induzione | (none) | before |
| recursive-call | la chiamata ricorsiva | (none) | before |
| definition | per definizione di | (none) | before |
| case | caso | (none) | before |
| base | base | (none) | before |
| inductive | induttivo | (none) | before |
| contradiction | per contraddizione | (none) | before |
| back | tornando alla definizione di | (none) | before |
| in | in | (none) | before |
| by-induction | per induzione | (none) | before |
| by-cases | per casi | (none) | before |
| on | su | (none) | before |
| all-cases | in tutti i casi | (none) | before |
| no-element | non c'è nessun elemento di | (none) | before |
| to-prove | per dimostrare | (none) | before |
| exhaustive | essendo questi casi esaustivi | (none) | before |
| fix | fix | (none) | before |
| argument | argomento | (none) | before |
| left-right | da sinistra a destra | (none) | before |
| right-left | da destra a sinistra | (none) | before |
| not-translated | non tradotto | (none) | before |

Read only: sia (var); siano (var); consideriamo (var); se (hyp); supponiamo (hyp); assumiamo (hyp); da (fact); usando (fact); poiché (fact); grazie a (fact); cioè (fact); allora (claim); mostriamo (claim); dimostriamo (claim); abbiamo (claim); quindi (claim); dunque (claim); ne segue (claim); ne deduciamo (claim); otteniamo (claim); basta (back); è sufficiente (back); si riduce a (back); equivale a dimostrare (back); basta dimostrare (back); basta mostrare (back); è sufficiente dimostrare (back).

### Korean (ko)

| use | phrase | role | side |
|---|---|---|---|
| let | 라 하자 | var | after |
| let-plural | 라 하자 | var | after |
| consider | 임의의 | var | before |
| choose | 임의로 택한 | var | before |
| assume | 라고 가정하자 | hyp | after |
| we-prove | 임을 보이자 | claim | after |
| prove | 임을 보여야 한다 | claim | after |
| proved | 임을 보였다 | claim | after |
| have | 이다 | claim | after |
| thus-have | 그러므로 | claim | before |
| get | 임을 얻는다 | claim | after |
| particular | 특히 | claim | before |
| deduce | 따라서 | claim | before |
| can-deduce | 임을 유도할 수 있다 | claim | after |
| so | 그러므로 | claim | before |
| from | 로부터 | fact | after |
| since | 이므로 | fact | after |
| using | 을(를) 이용하여 | fact | after |
| that-is | 즉 | fact | before |
| witness | 증인 | fact | before |
| by-induction-on | 에 대한 귀납법으로 | fact | after |
| by-cases-on | 에 대한 경우 분석으로 | fact | after |
| generalise | 로 일반화한다 | fact | after |
| recursion | 에 대한 재귀로 | fact | after |
| rewriting | 을(를) 이용하여 다시 쓰면 | fact | after |
| the-term | 항 | fact | before |
| and | 그리고 | (none) | before |
| by | 에 의해 | (none) | after |
| arbitrary | 는 임의이다 | (none) | before |
| ih | 귀납 가정에 의해 | (none) | before |
| recursive-call | 재귀 호출 | (none) | before |
| definition | 의 정의에 의해 | (none) | after |
| case | 경우 | (none) | before |
| base | 기저 | (none) | before |
| inductive | 귀납 | (none) | before |
| contradiction | 모순에 의해 | (none) | before |
| back | 의 정의로 돌아가서 | (none) | after |
| in | 에서 | (none) | after |
| by-induction | 귀납법으로 | (none) | before |
| by-cases | 경우 분석으로 | (none) | before |
| on | 에 대하여 | (none) | after |
| all-cases | 모든 경우에 | (none) | before |
| no-element | 의 원소는 없다 | (none) | after |
| to-prove | 을(를) 보이기 위해 | (none) | after |
| exhaustive | 이 경우들이 전부이므로 | (none) | before |
| fix | fix | (none) | before |
| argument | 인수 | (none) | before |
| left-right | 왼쪽에서 오른쪽으로 | (none) | before |
| right-left | 오른쪽에서 왼쪽으로 | (none) | before |
| not-translated | 번역되지 않음 | (none) | before |

Read only: 이면 (hyp); 임을 보이면 충분하다 (back); 로 귀결된다 (back).

### Latin (la)

| use | phrase | role | side |
|---|---|---|---|
| let | sit | var | before |
| let-plural | sint | var | before |
| consider | consideremus quodlibet | var | before |
| choose | eligamus quaelibet | var | before |
| assume | ponamus | hyp | before |
| we-prove | ostendamus | claim | before |
| prove | ostendendum est | claim | before |
| proved | ostendimus | claim | before |
| have | habemus | claim | before |
| thus-have | ergo habemus | claim | before |
| get | obtinemus | claim | before |
| particular | speciatim | claim | before |
| deduce | unde sequitur | claim | before |
| can-deduce | deducere possumus | claim | before |
| so | ergo | claim | before |
| from | ex | fact | before |
| since | quoniam | fact | before |
| using | adhibentes | fact | before |
| that-is | id est | fact | before |
| witness | cum teste | fact | before |
| by-induction-on | per inductionem in | fact | before |
| by-cases-on | per casus in | fact | before |
| generalise | generalizamus ad | fact | before |
| recursion | per recursionem in | fact | before |
| rewriting | rescribentes per | fact | before |
| the-term | terminus | fact | before |
| and | et | (none) | before |
| by | per | (none) | before |
| arbitrary | quodlibet est | (none) | before |
| ih | per hypothesim inductionis | (none) | before |
| recursive-call | vocatio recursiva | (none) | before |
| definition | ex definitione | (none) | before |
| case | casus | (none) | before |
| base | basis | (none) | before |
| inductive | gradus | (none) | before |
| contradiction | per absurdum | (none) | before |
| back | redeuntes ad definitionem | (none) | before |
| in | in | (none) | before |
| by-induction | per inductionem | (none) | before |
| by-cases | per casus | (none) | before |
| on | in | (none) | before |
| all-cases | in omnibus casibus | (none) | before |
| no-element | nullum elementum est | (none) | before |
| to-prove | ut ostendamus | (none) | before |
| exhaustive | his casibus exhaustis | (none) | before |
| fix | fix | (none) | before |
| argument | argumentum | (none) | before |
| left-right | a sinistra ad dextram | (none) | before |
| right-left | a dextra ad sinistram | (none) | before |
| not-translated | non translatum | (none) | before |

Read only: sit (var); sint (var); si (hyp); supponamus (hyp); tum (claim); igitur (claim); sufficit ostendere (back); quod idem est ac (back).

### Dutch (nl)

| use | phrase | role | side |
|---|---|---|---|
| let | laat | var | before |
| let-plural | laat | var | before |
| consider | beschouw een willekeurige | var | before |
| choose | kies willekeurig | var | before |
| assume | stel | hyp | before |
| we-prove | we bewijzen | claim | before |
| prove | te bewijzen | claim | before |
| proved | we hebben bewezen | claim | before |
| have | er geldt | claim | before |
| thus-have | dus geldt | claim | before |
| get | we krijgen | claim | before |
| particular | in het bijzonder | claim | before |
| deduce | hieruit volgt | claim | before |
| can-deduce | kunnen we afleiden | claim | before |
| so | dus | claim | before |
| from | uit | fact | before |
| since | omdat | fact | before |
| using | met behulp van | fact | before |
| that-is | dat wil zeggen | fact | before |
| witness | met getuige | fact | before |
| by-induction-on | met inductie naar | fact | before |
| by-cases-on | met gevalsonderscheiding naar | fact | before |
| generalise | veralgemenen we het tot | fact | before |
| recursion | met recursie naar | fact | before |
| rewriting | herschrijven met | fact | before |
| the-term | de term | fact | before |
| and | en | (none) | before |
| by | volgens | (none) | before |
| arbitrary | willekeurig is | (none) | before |
| ih | volgens de inductiehypothese | (none) | before |
| recursive-call | de recursieve aanroep | (none) | before |
| definition | volgens de definitie van | (none) | before |
| case | geval | (none) | before |
| base | basis | (none) | before |
| inductive | inductief | (none) | before |
| contradiction | uit het ongerijmde | (none) | before |
| back | terug naar de definitie van | (none) | before |
| in | in | (none) | before |
| by-induction | met inductie | (none) | before |
| by-cases | met gevalsonderscheiding | (none) | before |
| on | naar | (none) | before |
| all-cases | in alle gevallen | (none) | before |
| no-element | er is geen element van | (none) | before |
| to-prove | om te bewijzen | (none) | before |
| exhaustive | deze gevallen zijn uitputtend | (none) | before |
| fix | fix | (none) | before |
| argument | argument | (none) | before |
| left-right | van links naar rechts | (none) | before |
| right-left | van rechts naar links | (none) | before |
| not-translated | niet vertaald | (none) | before |

Read only: zij (var); laat (var); als (hyp); stel (hyp); dan (claim); hebben we (claim); geldt (claim); het volstaat te bewijzen dat (back); het volstaat te bewijzen (back); dit komt neer op (back).

### Russian (ru)

| use | phrase | role | side |
|---|---|---|---|
| let | пусть | var | before |
| let-plural | пусть | var | before |
| consider | рассмотрим произвольное | var | before |
| choose | выберем произвольно | var | before |
| assume | предположим, что | hyp | before |
| we-prove | докажем, что | claim | before |
| prove | требуется доказать | claim | before |
| proved | мы доказали | claim | before |
| have | имеем | claim | before |
| thus-have | таким образом, имеем | claim | before |
| get | получаем | claim | before |
| particular | в частности | claim | before |
| deduce | следовательно | claim | before |
| can-deduce | можно вывести | claim | before |
| so | тогда | claim | before |
| from | из | fact | before |
| since | поскольку | fact | before |
| using | используя | fact | before |
| that-is | то есть | fact | before |
| witness | со свидетелем | fact | before |
| by-induction-on | индукцией по | fact | before |
| by-cases-on | разбором случаев по | fact | before |
| generalise | обобщим до | fact | before |
| recursion | рекурсией по | fact | before |
| rewriting | переписывая с помощью | fact | before |
| the-term | терм | fact | before |
| and | и | (none) | before |
| by | по | (none) | before |
| arbitrary | произвольно | (none) | before |
| ih | по предположению индукции | (none) | before |
| recursive-call | рекурсивный вызов | (none) | before |
| definition | по определению | (none) | before |
| case | случай | (none) | before |
| base | база | (none) | before |
| inductive | шаг | (none) | before |
| contradiction | от противного | (none) | before |
| back | возвращаясь к определению | (none) | before |
| in | в | (none) | before |
| by-induction | индукцией | (none) | before |
| by-cases | разбором случаев | (none) | before |
| on | по | (none) | before |
| all-cases | во всех случаях | (none) | before |
| no-element | нет элементов типа | (none) | before |
| to-prove | чтобы доказать | (none) | before |
| exhaustive | эти случаи исчерпывают все возможности | (none) | before |
| fix | fix | (none) | before |
| argument | аргумент | (none) | before |
| left-right | слева направо | (none) | before |
| right-left | справа налево | (none) | before |
| not-translated | не переведено | (none) | before |

Read only: если (hyp); то (claim); достаточно доказать, что (back); достаточно доказать (back); что равносильно (back).

Writing system: `punctuation "ru" "«".  punctuation "ru" "»". `

### Chinese (zh)

| use | phrase | role | side |
|---|---|---|---|
| let | 设 | var | before |
| let-plural | 设 | var | before |
| consider | 任取 | var | before |
| choose | 任意选取 | var | before |
| assume | 假设 | hyp | before |
| we-prove | 我们证明 | claim | before |
| prove | 需证 | claim | before |
| proved | 我们已证明 | claim | before |
| have | 我们有 | claim | before |
| thus-have | 因此我们有 | claim | before |
| get | 我们得到 | claim | before |
| particular | 特别地 | claim | before |
| deduce | 由此可得 | claim | before |
| can-deduce | 可以推出 | claim | before |
| so | 所以 | claim | before |
| from | 由 | fact | before |
| since | 因为 | fact | before |
| using | 利用 | fact | before |
| that-is | 即 | fact | before |
| witness | 取见证 | fact | before |
| generalise | 我们将其推广为 | fact | before |
| rewriting | 用等式改写 | fact | before |
| by-induction-on | 用归纳法，对 | (none) | before |
| by-cases-on | 分情形讨论，对 | (none) | before |
| recursion | 用递归，对 | (none) | before |
| the-term | 项 | (none) | before |
| and | 且 | (none) | before |
| by | 根据 | (none) | before |
| arbitrary | 是任意的 | (none) | before |
| ih | 根据归纳假设 | (none) | before |
| recursive-call | 递归调用 | (none) | before |
| definition | 根据定义 | (none) | before |
| case | 情形 | (none) | before |
| base | 基础 | (none) | before |
| inductive | 归纳 | (none) | before |
| contradiction | 根据矛盾 | (none) | before |
| back | 回到定义 | (none) | before |
| in | 于 | (none) | before |
| by-induction | 用归纳法 | (none) | before |
| by-cases | 分情形讨论 | (none) | before |
| on | 对 | (none) | before |
| all-cases | 在所有情形下 | (none) | before |
| no-element | 没有元素属于 | (none) | before |
| to-prove | 为证明 | (none) | before |
| exhaustive | 这些情形是穷尽的 | (none) | before |
| fix | fix | (none) | before |
| argument | 参数 | (none) | before |
| left-right | 从左到右 | (none) | before |
| right-left | 从右到左 | (none) | before |
| not-translated | 未翻译 | (none) | before |

Read only: 若 (hyp); 如果 (hyp); 则 (claim); 那么 (claim); 可得 (claim); 只需证明 (back); 即证 (back).

Writing system: `unspaced "zh". punctuation "zh" "，".  punctuation "zh" "。".  punctuation "zh" "：". punctuation "zh" "；".  punctuation "zh" "、".  punctuation "zh" "（".  punctuation "zh" "）". `
