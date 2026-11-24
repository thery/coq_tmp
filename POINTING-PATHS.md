# Subterm paths: how a selection names a subterm

Proof by pointing needs to know which subterm of the goal the mouse
selected.  With the path method, Rocq's printer itself tags each printed
subterm with its **path** (the option `Set Printing Subterm Paths` of the
prototype branch `path-tags` of Rocq), the goal panel reads the path of
the selected part, and sends it to `elpi point_run_path` (branch
`point-paths`).  Nothing is printed twice and no characters are counted.

The reference for the numbering is the comment above `kids` in
[pbp_select.v](pbp_select.v); this page explains it with examples.

## Dewey notation

A path is the list of the child indices taken from the root of the term
down to the subterm, written `i.j.k`.  The empty path, written `.`, is
the whole term (the conclusion, or the type of a hypothesis).

The children of each kind of term, as Rocq-Elpi sees terms:

| term | children |
|---|---|
| application `f x y` | 0 the head `f`, 1 `x`, 2 `y`, ... |
| `forall x : T, B`, `fun x : T => B` | 0 the type `T`, 1 the body `B` |
| `let x : T := v in B` | 0 `T`, 1 `v`, 2 `B` |
| `match e return R with b1 \| b2 ... end` | 0 `e`, 1 `R`, 2 the first branch, 3 the second, ... |
| a cast `(t : T)` | 0 `T`, 1 `t` |

An arrow `A -> B` is a `forall` whose variable is not used: 0 is `A`,
1 is `B`.  A branch of a `match` is a `fun` over the arguments of its
constructor: in `S k => e`, the branch is `fun k => e`, so `e` is child 1
of the branch.

## Examples

The tagged outputs below are those of the prototype printer (`Show.`
after `Set Printing Subterm Paths.`, the tags written `<P>...</P>` in the
terminal; in a goal panel they are invisible).

**`a + b = b + a`.**  Under its notations this is
`@eq nat (Nat.add a b) (Nat.add b a)`, an application of `eq` to three
arguments:

```
<><2><2.1>a</2.1> + <2.2>b</2.2></2> = <3><3.1>b</3.1> + <3.2>a</3.2></3></>
```

| path | subterm |
|---|---|
| `.` | `a + b = b + a` |
| `0` | `eq`, the head: it has no text of its own (the notation `=`) |
| `1` | `nat`, an implicit argument: not printed |
| `2` | `a + b` |
| `2.0` | `Nat.add`, the head (no text: the notation `+`) |
| `2.1` | the first `a` |
| `2.2` | the first `b` |
| `3` | `b + a` |
| `3.1` | the second `b` |
| `3.2` | the second `a` |

Selecting the first `a` sends `"2.1"`; selecting `b + a` sends `"3"`.

**`forall n : nat, n + 0 = n`.**

```
<>forall <>n</> : <0>nat</0>, <1><1.2><1.2.1>n</1.2.1> + <1.2.2>0</1.2.2></1.2> = <1.3>n</1.3></1></>
```

`0` is the type `nat`, `1` the body `n + 0 = n`, `1.2` is `n + 0`,
`1.2.1` its `n`, `1.2.2` its `0`, and `1.3` the `n` on the right.

**A hypothesis.**  With `H : A -> B` in the context, the path is taken in
the type of `H`, and the interface sends the name first: selecting `B`
sends `"H" "1"`.

**`let` and `match`.**

```
<>forall <>n</> : <0>nat</0>, <1>(<1.2>let <1.2>m</1.2> := <1.2.1>n</1.2.1> in <1.2.2>m</1.2.2></1.2>) = <1.3>match <1.3.0>n</1.3.0> with
                                      | 0 => <1.3.2>1</1.3.2>
                                      | S <1.3.3>k</1.3.3> => <1.3.3.1>k</1.3.3.1>
                                      end</1.3></1></>
```

- `1.2` is the `let`: its value `n` is `1.2.1`, its body `m` is `1.2.2`
  (its type, child 0, is not printed).
- `1.3` is the `match`: its scrutinee `n` is `1.3.0`, its first branch
  `1` is `1.3.2`, its second branch is `1.3.3`.  The second branch is
  `fun k => k`, so the bound name `k` of the pattern carries the path of
  the branch itself, and its body `k` is `1.3.3.1`.

## What cannot be selected

A subterm that has no text of its own cannot be selected with the mouse:
the head of a notation (`eq` at `0`, `Nat.add` at `2.0` above), an
implicit argument (`nat` at `1`), a hidden coercion (its argument keeps
its own path).  A selection made of several words is the innermost
subterm whose tag contains all of them: selecting `a + b` gives `2`,
selecting `+` alone gives `2` too (the symbol belongs to the notation's
node).

## In the page

In rocq-web and in VsRocq (the trials of branch `path-tags`), each word of
the goal carries the paths of the subterms it belongs to, outermost
first, in an attribute: the `b` of `b = a` is

```html
<span class="pp-constr-variable" data-paths=". 2">b</span>
```

(`.` the whole conclusion, `2` the `b` itself).
