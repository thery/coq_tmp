# dap: the debugger and the properties in VS Code

[← overview](../DESIGN.md) · README: [`../dap/README.md`](../dap/README.md)

## What

- `elpi-dap`, a debug adapter (Debug Adapter Protocol): VS Code's
  breakpoints (in the margin, on predicates), Step Into/Over/Out,
  Continue, Pause, Restart Frame, the call stack, the variables panel,
  the watch panel and the debug console work on Elpi programs, by driving
  `elpi-debug -machine`.
- the extension [`../dap/vscode`](../dap/vscode) (plain JavaScript): it
  starts the adapter, and shows the properties of elpi-check in the Test
  Explorer, with a "Debug this counterexample" action.

**Said plainly**: tested by scripted DAP sessions and in Node with a
stand-in for the `vscode` module; nobody has clicked in VS Code yet.

## How

```
  VS Code ──DAP (Content-Length framed JSON)──▶ elpi-dap ──commands (c, s, o, l, r N, + clause N …)──▶ elpi-debug -machine
          ◀──responses, events (stopped, output)──      ◀──@@elpi-debug {JSON} at each stop, + text──
                                                         (SIGUSR1 = pause)
```

The adapter ([`../dap/lib`](../dap/lib), OCaml) is one loop waiting on
VS Code and on elpi-debug: `wire.ml` (the two framings), `protocol.ml`
(DAP messages), `debuggee.ml` (the child process, its JSON as OCaml
data), `breakpoints.ml` (a line → the rule that holds it, from the
listing elpi-debug prints first), `session.ml` (the mapping).

The mapping, from [`session.ml`](../dap/lib/session.ml)'s header:

```
   - setBreakpoints (file:line): + clause N, N the rule (or CHR rule) that
     holds the line;
     setFunctionBreakpoints: + P, a breakpoint on the predicate P;
   - stepIn: c (creep); next: s (skip) at the ports of a call, c at a step
     inside a call (unify, pi, =>, cut, delay); stepOut: o; continue: l
     (leap); restartFrame: r N (retry the call N); pause: SIGUSR1;
```

elpi-debug answers each command with a description of the stop (the same
number when the command only showed something, a new one when the run
went on); the session keeps, in order, what it expects from each command
sent, so the text printed before an answer belongs to the command that
caused it.

A session, from the committed transcript
[`../dap/tests/sessions.t`](../dap/tests/sessions.t) (lines cut at `…`):
a breakpoint on line 6 of `append.elpi` (its second clause), then Step
Into:

```
  -> {"seq":3,"type":"request","command":"setBreakpoints","arguments":{"source":{"path":"append.elpi"},"breakpoints":[{"line":6},{"line":2}]}}
  <- {"seq":4,"type":"response",…,"body":{"breakpoints":[{"verified":true,"line":6},{"verified":false,"message":"no clause at this line"}]}}
  …
  <- {"seq":7,"type":"event","event":"output","body":{"category":"stdout","output":"Unify: #1 with append.elpi:6: append [1, 2] [3] [1 | X1]\n"}}
  <- {"seq":8,"type":"event","event":"output","body":{"category":"stdout","output":"      X0 := [1 | X1]\n"}}
  <- {"seq":9,"type":"event","event":"stopped","body":{"reason":"breakpoint","description":"Unify step",…
  -> {"seq":6,"type":"request","command":"stackTrace","arguments":{"threadId":1}}
  <- {"seq":11,…,"body":{"stackFrames":[{"name":"Unify: #1 append [1, 2] [3] [1 | X1]","id":1,"column":1,"source":{"name":"append.elpi","path":"append.elpi"},"line":6}],"totalFrames":1}}
  # Step in: the call port of the recursive call.
  -> {"seq":9,"type":"request","command":"stepIn","arguments":{"threadId":1}}
  <- {"seq":15,"type":"event","event":"output","body":{"category":"stdout","output":"  Call: #2 append [2] [3] X1   (premise 1 of append.elpi:6)\n"}}
  <- {"seq":16,"type":"event","event":"stopped","body":{"reason":"step","description":"Call port",…
  <- {"seq":17,…,"body":{"stackFrames":[{"name":"Call: #2 append [2] [3] X1","id":2,"column":25,…
```

A call at its call port is placed at the goal it comes from (column 25,
`append L M R` in line 6), so the editor highlights that premise only:
that is what `reflect.premises` is for.  The scopes of a frame: **Goal**
(arguments with modes, the bindings of the step), **Query** (the
variables of the query by their names), **Local program (=>)**,
**Eigenvariables**, **Constraints** (the CHR store, `[S2] = leq X1 X2`).

### The Test Explorer

[`../dap/vscode/properties.js`](../dap/vscode/properties.js) runs
`elpi-check -json -list FILE` when an `.elpi` file is opened or saved (the
checker's own analysis: a property is found when Elpi compiles it), one
test per property; running a test is `elpi-check -json -p NAME FILE`,
whose report ([`../check/README.md`](../check/README.md), "The report
for tools") gives the status, the shrunk counterexample and the replay
goal.  "Debug this counterexample" starts the debugger on the replay
goal, stopped on entry: for `sort-length` of
[`../demo/lists.elpi`](../demo/lists.elpi) the report gives

```
"replay": "sort [0, 0] S, std.length [0, 0] N, std.length S M, N = M"
```

and the run under the debugger ends with

```
Deepest failure (depth 2): 0 < 0
  called from:
    #5 insert 0 [0] [0, 0]
    #1 sort [0, 0] [0, 0]
  a builtin (not a predicate of the program): it ran natively and failed
```

(the clause of the bug drops the second 0).

## Why this way

- **An adapter over `-machine`, not the debugger inside the adapter.**
  elpi-debug stays a command-line tool, testable with cram files; the
  adapter is a thin translation, testable by scripted sessions; the JSON
  carries everything a stop shows, so the adapter never parses text for
  a person.  The cost: one process more, and a pause by signal (the
  interpreter asks at each event).
- **The model of SWI-Prolog's DAP server** (Eshel Yaron): the ports of the
  box are where a run stops, a stack frame is a call, Restart Frame is
  retry.
- **A separate extension**, not a change to gares.elpi-lang (the language
  server and trace viewer): merging is the decision of its author; the
  README lists what it would take (about 55 lines of `debugger.js` and the
  contributions of `package.json`).
- **The checker's report as JSON lines** rather than parsing its human
  report: the Test Explorer gets exact counts, values in source syntax,
  the replay goal.
- **Limits** (README): interactive mode is slow (`std.iota 200 L,
  naive-rev L R1, rev L R2`: 1.5 s alone, 10.1 s with `-machine`), a
  variable may be named differently in two panels (requested feature 2),
  breakpoints changed while running take effect at the next stop.
