# An algebra of selectors (draft)

A selector denotes a set of positions of a term: `⟦s⟧ t ⊆ Paths(t)`. It is
built from a few blocks and operators. Every ssreflect pattern is a
combination of them, and the laws below say when a combination can be
flattened back into a single ssreflect pattern.

## Blocks

| block | written | denotes, in a term `t` |
|---|---|---|
| root | `ε` | `{ε}`, the whole term |
| step | `i` | `{i}`, the i-th immediate subterm (kids: app head 0, args 1…) |
| match | `⟨p⟩` | the occurrences of the first instance of the term pattern `p`: first pre-order match keyed by the head of `p`, then all subterms equal to it |
| hole | `⟨C | X⟩` | the `X` positions inside the occurrences of the first instance of `C` |

`⟨p⟩` is ssreflect's B and `⟨C | X⟩` is its C1.

## Operators

| operator | written | denotes |
|---|---|---|
| then | `s ; s'` | `{ π·π' | π ∈ ⟦s⟧ t, π' ∈ ⟦s'⟧ (t at π) }`: `s'` read inside each place `s` gives |
| pick | `s # K` | the positions of `⟦s⟧ t` whose rank, in pre-order, is in `K` (`K` a set of ranks, or its complement `−K`) |
| union | `s ∪ s'` | `⟦s⟧ t ∪ ⟦s'⟧ t` |
| name | `N := s` | an abbreviation |

## ssreflect patterns as combinations

| ssreflect | kind | combination |
|---|---|---|
| `"2.3.1"` | A1 path | `2 ; 3 ; 1` |
| `{k}t` | A2 occurrence | `⟨t⟩ # {k}` (where `t` has no hole) |
| `[t]` | B | `⟨t⟩` |
| `[X in C]` | C1 | `⟨C | X⟩` |
| `[t in X in C]` | C2 | `⟨C | X⟩ ; ⟨t⟩` |
| `[t as X in C]` | C3 | `⟨C[t/X] | X⟩` |
| `[in X in C]` | D2 | `⟨C | X⟩ ; ⟨redex of the rule⟩` |
| `{1 3}[…]` | E1 | `[…] # {1,3}` |
| `RHS` | E2 | `RHS := ⟨_ = X | X⟩` |

ssreflect allows one `;` after a hole (C2, D2) and one `#` at the top. The
algebra allows any number of each.

## Laws

1. **Paths.** `ε ; s = s ; ε = s`, `(s ; s') ; s'' = s ; (s' ; s'')`. A path is
   a chain of steps.
2. **Hole of a fixed context.** If `C` has no hole other than `X` (`C` fully
   given), `⟨C | X⟩` is the X position of the occurrences of `C`. When `C`
   occurs once, it is a path.
3. **Flattening holes, with a side condition.**
   `⟨C₁ | X⟩ ; ⟨C₂ | Y⟩` and `⟨C₁[C₂/X] | Y⟩` are **not** equal in general.
   The left one takes the first instance of `C₁`, then looks for `C₂` inside
   its `X` part, and fails if `C₂` is not there. The right one takes the first
   instance of the whole `C₁[C₂/X]`, which may be a later `C₁`. They are equal
   when the first instance of `C₁` has an instance of `C₂` in its `X` part.
   For example, in `f a 1 + f b (g 2) = 0`, `⟨f _ X | X⟩ ; ⟨g Y | Y⟩` fails,
   because the first `f _ _` is `f a 1` and `1` contains no `g`, while
   `⟨f _ (g Y) | Y⟩` gives `2`.
4. **as = hole with the redex put in.** `⟨C | X⟩` restricted to the places
   that match `t` is `⟨C[t/X] | X⟩` (C3), with no side condition, because C3 is
   matched in one step.
5. **pick.** `s # K # K' = s # K'∘K` (ranks of ranks). `s # {1..n} = s`
   when `⟦s⟧` has `n` positions.
6. **Univocal.** `s` is univocal on `t` when `|⟦s⟧ t| = 1`. `s # {k}` is always
   univocal or empty: that is why occurrence numbers always "work", and why
   they say nothing.

## Translation to ssreflect

`to_ssr s` rewrites `s` with the laws until it has the form
`⟨…⟩`, `⟨C | X⟩`, `⟨C | X⟩ ; ⟨t⟩` or one of these followed by `# K`. It
uses law 3 only when its side condition holds on the goal at hand. Otherwise
it reports that `s` has no ssreflect form, or gives the flattened pattern
with a warning that it means something else on other goals.

## Size and the "best" selector

`size s` counts the symbols kept: the non-hole nodes of the patterns, plus
the steps, plus a large weight per pick (`#`). The best selector of a position
`π` is a univocal `s` with `⟦s⟧ t = {π}` and the least `size`. For one hole
`⟨C | X⟩`, the smallest `C` comes from anti-unification: keep, for each earlier
subterm with the same key, one place where it differs from the target (a
smallest hitting set).
