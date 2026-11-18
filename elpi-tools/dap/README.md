# elpi-dap: the Elpi debugger in VS Code

`elpi-dap` is a debug adapter: it speaks the
[Debug Adapter Protocol](https://microsoft.github.io/debug-adapter-protocol/)
(DAP) with VS Code, and runs the debugger
[`elpi-debug`](../debug/README.md) on the program.  With the small
extension of [`vscode/`](vscode), VS Code's usual debugging interface
works on Elpi programs: breakpoints in the margin of `.elpi` files and on
predicates, Step Into, Step Over, Step Out, Continue, Pause, Restart
Frame, the call stack, the variables panel, the debug console.  Standalone
Elpi 4.0.0 only (opam switch `elpi5`), not Rocq-Elpi.

It follows the idea of Eshel Yaron's
[DAP server for SWI-Prolog](https://github.com/eshelyaron/debug_adapter):
the ports of Prolog's box model are the places where the run stops, a
stack frame is a call, Restart Frame is Prolog's retry.

**What was tested.**  The adapter is tested by scripted DAP sessions: a
small client ([`tests/dap_replay.ml`](tests/dap_replay.ml)) sends the
requests VS Code would send and the transcripts are compared with the
committed ones ([`tests/sessions.t`](tests/sessions.t),
[`tests/demo.t`](tests/demo.t), run by `dune build @runtest`).  The
extension was only loaded in Node with a stand-in for the `vscode` module
(it starts the adapter built next to it and fills in the path of
elpi-debug).  **Nobody has clicked in VS Code yet**: what VS Code shows
below is what the protocol says it shows, not something seen.

## Install

    cd elpi-tools && dune build          # builds _build/install/default/bin/elpi-dap and elpi-debug
    ln -s $PWD/dap/vscode ~/.vscode/extensions/elpi-tools.elpi-tools-0.1.0

then restart VS Code.  The extension starts the `elpi-dap` built next to
it (`elpi-tools/_build/install/default/bin`), else the one of the PATH;
the settings `elpiTools.adapterPath` and `elpiTools.elpiDebugPath` choose
others.  It needs no build (plain JavaScript) and no other extension; with
[gares.elpi-lang](https://github.com/LPCIC/elpi-lang) installed, its
syntax colouring and language server work alongside.

A launch configuration (`.vscode/launch.json` of the folder):

```json
{
  "version": "0.2.0",
  "configurations": [
    {
      "name": "append",
      "type": "elpi",
      "request": "launch",
      "program": "${workspaceFolder}/append.elpi",
      "goal": "append [1,2] [3] L",
      "args": [],
      "stopOnEntry": false
    }
  ]
}
```

`args` are more options of elpi-debug (`-I DIR`, `-all` for all the
solutions, `-profile`...).  Without a launch.json, F5 on an `.elpi` file
asks for the goal.

**What one should see** (from the protocol, not seen): with a breakpoint
on line 6 of [`tests/append.elpi`](tests/append.elpi) (its second clause),
F5 stops with line 6 highlighted, the call stack showing `Unify: #1 append
[1, 2] [3] [1 | X1]`, and in the variables panel the scope **Goal**: `goal`,
`arg 1 (input) = [1, 2]`, `arg 2 (input) = [3]`, `arg 3 (output) = [1 |
X1]`, `X0 := [1 | X1]`.  Step Into stops at `Call: #2 append [2] [3] X1`, the
stack showing #2 above #1; the debug console shows each event as the
trace of elpi-debug does, and the solutions at the end.  Typing a command
of elpi-debug in the debug console (`g`, `p`, `scope`, `hyps`, `e`, `f`,
`+ P`...) runs it.

## The mapping

| DAP | elpi-debug |
|---|---|
| setBreakpoints (file, line) | `+ clause N`: N is the rule that holds the line; the run stops at the unify step of that rule (when it is selected for a call) |
| setFunctionBreakpoints (name) | `+ P`: the run stops at the call port of each call of P (and at the resume of a goal of P woken by CHR) |
| configurationDone | `l` (leap to the first breakpoint), or with `stopOnEntry` a stop before the first event |
| stepIn | `c` (creep: the next event) |
| next | `s` (skip the call) at the ports of a call; `c` at a step inside a call (unify, pi, `=>`, cut, delay), where skip would leave the call |
| stepOut | `o`: to the exit or fail port of the call whose body runs the event (at a port of a call: the call above) |
| continue | `l` (leap) |
| pause | the signal SIGUSR1: the run stops at its next event |
| restartFrame (call #N) | `r N`: retry call #N from its call port (bindings, local program and scope undone) |
| evaluate (debug console) | the command typed, its output as the answer |
| stackTrace | the calls of the stop, the call in focus first, named `#N goal` (the first one prefixed by the port: `Call:`, `Unify:`, `Pi:`...); each at the line of the clause it runs; the call in focus at its own ports (call, exit, redo, fail), where it runs no clause, at the clause of its caller, where the goal is written; a call that runs a hypothetical clause has no source line |
| scopes | **Goal**: the goal, its arguments with their modes, and at a unify step the bindings it made (`X0 := ...`, with the pruning, if any); **Local program (=>)**: the clauses added by `=>`, each with the call that added it; **Eigenvariables**: those in force, and for each logic variable of the goal the eigenvariables it may depend on |
| stopped | reason `breakpoint`, `step`, `pause` or `entry`; the description says the port (`Call port`, `Unify step`...), the text is the event |
| output | every line elpi-debug prints that is not for the adapter: the events shown, the prints of the program, the solutions, the explanation of a failure, the profile |
| exited, terminated | when elpi-debug ends |

A source line belongs to the last item of its file that starts at or
before it (a rule or a declaration, from the listing of elpi-debug); a
breakpoint is set when that item is a rule, and VS Code moves it to the
first line of the rule.

## How it works

`elpi-debug -machine` ([`../debug/lib/machine.elpi`](../debug/lib/machine.elpi))
prints, besides its usual text, lines `@@elpi-debug {JSON}`: first the
listing of the program (its rules, numbered, with file and line; the lines
of its declarations), then at each stop, in place of the prompt, the
description of the stop: its number, its reason, the event, the stack
(each call with the clause it runs, its arguments, the scope of its
variables), the bindings of a unify step, the local program, the
eigenvariables.  It waits at a stop `Start` before the first event, where
the adapter sets the breakpoints.  The adapter never parses the text for a
person: it forwards it as output.

The adapter ([`lib/`](lib)) is one loop ([`bin/elpi_dap_main.ml`](bin/elpi_dap_main.ml))
waiting on VS Code and on elpi-debug:

- [`wire.ml`](lib/wire.ml): the two wire formats, DAP messages
  (`Content-Length` framing) and lines;
- [`protocol.ml`](lib/protocol.ml): DAP requests, responses, events;
- [`debuggee.ml`](lib/debuggee.ml): elpi-debug as a child process, and
  its messages as OCaml data;
- [`breakpoints.ml`](lib/breakpoints.ml): from a line to its rule;
- [`session.ml`](lib/session.ml): the requests and the messages.
  elpi-debug answers each command with a description of the stop (the same
  number when the command only showed something or changed a breakpoint,
  a new one when the run went on); the session keeps, in order, what it
  expects from each command sent, so the text printed before an answer
  belongs to the command that caused it (shown, hidden for a breakpoint
  change, or returned for the debug console).

OCaml, as elpi-debug's driver, with `yojson` (in the switch) for JSON;
no other dependency.

## Tests

`dune build @runtest` plays the scripts [`tests/*.dap`](tests) (one JSON
request per line, `{"await": E}` to wait for an event) with
`dap_replay` and compares the transcripts:

- [`tests/sessions.t`](tests/sessions.t): breakpoints on a clause and on
  a line without one, the stack, the scopes, step in, next, step out, the
  debug console, restart frame, continue (append); stop on entry, pi and
  `=>`, the three scopes, a frame running a hypothetical clause, `f` from
  the console (λ-calculus); a function breakpoint met at a call and at
  the resume of a goal suspended by CHR; a program that does not exist;
  a pause of a long run (only its reason is compared: where it stops
  depends on timing);
- [`tests/demo.t`](tests/demo.t): the seven configurations of the demo
  ([`../demo/.vscode/launch.json`](../demo/.vscode/launch.json)), below.

Not tested: VS Code itself (clicking, what its panels show), the
extension inside VS Code.

## The demo in VS Code

**Not tested by clicking**: the steps below are those of the scripted
sessions of [`tests/demo.t`](tests/demo.t), which check what the adapter
answers at each step; what VS Code draws from it is not checked.

1. Build and install as above; open the folder `elpi-tools/demo` in VS
   Code (File, Open Folder).  Its [`.vscode/launch.json`](../demo/.vscode/launch.json)
   has seven configurations, for the goals of [`../demo/DEMO.md`](../demo/DEMO.md).
2. **The wrong reduction.**  Open `lambda.elpi`, click in the margin of
   line 26 (`step (app M _) M.`, the wrong rule): a red dot.  In Run and
   Debug, pick "1. The wrong reduction (breakpoint on line 26)" and press
   F5.  The debug console shows `Solution 1: N = c`; then the run stops on
   line 26, the call stack shows `Unify: #1 step (app (lam c0 \ c) c) (lam
   c0 \ c)`, and Goal shows `X0 := lam c0 \ c`: the rule that drops the
   argument.  Continue: `Solution 2: N = lam c0 \ c`, then (with `-all`)
   the search for a third ends with the explanation of its failure.
3. **Hypotheses and eigenvariables.**  Pick "2. ..." (stops on entry,
   before the first event).  Press Step Into ten times: the debug console
   shows `Call`, `Unify`, `Pi: x#1 is a new eigenvariable`, `Assume: of x#1
   X1`, the same for #2, then `Call: #3 of x#1 X4` and `Unify: #3 with
   hypothesis added by #1`.  The call stack shows #3 (no source line: it
   runs a hypothesis), #2 and #1 at line 20.  Variables: Goal `X4 := X1`;
   Local program (=>) `of x#2 X0: hypothesis added by #2`, `of x#1 X1:
   hypothesis added by #1` (Elpi's printer may name one variable
   differently in two places: `X0` here is the `X3` of the Assume line);
   Eigenvariables `x#1`, `x#2`, `X1: may depend on no eigenvariable`.
4. **A failure.**  Pick "3. ..." and press Continue: the debug console
   shows the explanation: the deepest failure `#4 of x#1 X5`, the
   hypothesis added by #1 that fails on the occurs check.
5. **A predicate defined nowhere.**  In the Breakpoints panel, `+`
   (Function Breakpoint), type `positive`.  Pick "4. ..." and F5: the run
   stops at `Call: #2 positive 1`; Step Into: `Fail: #2 positive 1`;
   Continue: the warning and the explanation (`positive is declared but
   has no clause at all`).
6. **Sorting.**  Open `lists.elpi`, a breakpoint on line 10 (`insert X [Y |
   L] [Y | L] :- X = Y.`).  Pick "5. ..." and F5: it stops on line 10 at
   `Unify: #5 insert 0 [0] [0]`, the call stack shows `#1 sort [0, 0] [0]`
   at line 16 below it; Step Out: `Exit: #5 insert 0 [0] [0]`; Continue:
   `S = [0]`, an element lost.
7. **A sorting failure.**  Pick "6. ...": the run ends with the
   explanation, the deepest failure `0 < 0` called from `#5 insert 0 [0]
   [0, 0]`.
8. **The profile.**  Pick "7. ...": after the run (about 10 s on this
   laptop, see Limits) the debug console shows the profile: `append` 20 100
   calls for the naive reverse, `rev-onto` 201.

## Integration into the Elpi extension

This extension is separate from [gares.elpi-lang](https://github.com/LPCIC/elpi-lang)
(the language server and the trace viewer); merging them is the decision
of its author.  It would take: the `debuggers` and `breakpoints`
contributions of [`vscode/package.json`](vscode/package.json) and its
settings added to elpi-lang's `package.json` (the language `elpi` is
already declared there); [`vscode/debugger.js`](vscode/debugger.js) (about
70 lines: a factory that starts `elpi-dap`, a provider that completes the
launch configurations) called from elpi-lang's `activate`; and a way to
find `elpi-dap` (a setting, as here, or the binaries of an opam package
`elpi-tools`).  The extension is one entry point
([`vscode/extension.js`](vscode/extension.js)) and one module per tool, so
that the properties of [`elpi-check`](../check/README.md) can be added as
another module.

## Limits (said plainly)

- **Speed.**  Under the adapter, elpi-debug runs in interactive mode, which
  looks at every event even when it does not stop: measured on the
  laptop, `std.iota 200 L, naive-rev L R1, rev L R2` takes 1.5 s with
  `elpi-debug` alone, 9.6 s with `-i`, 10.1 s with `-machine` (the cost of
  `-i`, mostly printing each goal into the text of each event, even when
  the event is not shown; the adapter adds 5%).
- Breakpoints changed while the program runs take effect at the next stop
  (elpi-debug reads commands only at a stop).
- The comment lines just after a rule count as part of it (a breakpoint
  there stops on the rule).  No conditional breakpoints, hit counts,
  logpoints, data breakpoints, hovers, or changes of variables.  One
  thread.
- Logic variables are printed by Elpi's printer, which may give one
  variable different names in two places (two panels, or two lines).
- Under a directory named `_build` (as in dune's sandbox), Elpi's file
  resolver gives the program paths that do not exist, and breakpoints on
  lines are not found there (the tests run in a copy of their files).
- Inherited from elpi-debug: a cut through a variable, conjunctions of
  more than 16 goals, `=!=>`, CHR at depth 1 only (see
  [`../debug/README.md`](../debug/README.md), Limits).
