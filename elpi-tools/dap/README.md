# elpi-dap: the Elpi debugger in VS Code, and the properties in the Test Explorer

How it works and why, with the other tools: [`../DESIGN.md`](../DESIGN.md) (this part: [`../design/dap.md`](../design/dap.md)).

`elpi-dap` is a debug adapter: it speaks the
[Debug Adapter Protocol](https://microsoft.github.io/debug-adapter-protocol/)
(DAP) with VS Code, and runs the debugger
[`elpi-debug`](../debug/README.md) on the program.  With the small
extension of [`vscode/`](vscode), VS Code's usual debugging interface
works on Elpi programs: breakpoints in the margin of `.elpi` files and on
predicates, Step Into, Step Over, Step Out, Continue, Pause, Restart
Frame, the call stack, the variables panel, the debug console.  Standalone
Elpi 4.0.0 only, not Rocq-Elpi.

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
elpi-debug); its part for the properties of elpi-check (below, "The
properties in the Test Explorer") is tested in Node with a stand-in for
the `vscode` module and the real elpi-check.  **Nobody has clicked in VS
Code yet**: what VS Code shows below is what the protocol and the API say
it shows, not something seen.

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
solutions, `-profile`...).  A configuration with no `goal` asks for it
when it starts (with `"program": "${file}"`, a goal of the file being
edited: the demo's configuration 0); without a launch.json, F5 on an
`.elpi` file does the same.

**What one should see** (from the protocol, not seen): with a breakpoint
on line 6 of [`tests/append.elpi`](tests/append.elpi) (its second clause),
F5 stops with line 6 highlighted, the call stack showing `Unify: #1 append
[1, 2] [3] [1 | X1]`, and in the variables panel the scope **Goal**: `goal`,
`arg 1 (input) = [1, 2]`, `arg 2 (input) = [3]`, `arg 3 (output) = [1 |
X1]`, `X0 := [1 | X1]`, and the scope **Query**: `L = [1 | X1]`.  Step
Into stops at `Call: #2 append [2] [3] X1   (premise 1 of append.elpi:6)`,
the stack showing #2 above #1, both at the goal `append L M R` of line 6,
highlighted alone (the place of the premise, a range: column 25 to 37);
the debug console shows each event as the trace of elpi-debug does, and
the solutions at the end.  Typing a command of elpi-debug in the debug
console (`g`, `p`, `scope`, `hyps`, `e`, `f`, `+ P`...) runs it.  In the
Watch panel, `L` shows the value of the query's `L` at each stop, `X1`
that of the variable `X1` while it is in view (bound by the step, or in
a goal of the stack); at the exit port of a call seen at its call port,
the Goal scope lists what the whole call bound (`X0 := [1, 2, 3]` at the
exit of #1).  Variables keep their name `X<n>` for the whole run.

On a CHR program ([`tests/leq.elpi`](tests/leq.elpi), `leq A B, leq B C,
leq C A`), a breakpoint on line 9 (the transitivity rule) stops at
`Rule: clause 9 leq.elpi:9 tried on [S1, S2]` with line 9 highlighted,
the scope **Constraints** showing `[S2] = leq X1 X2`, `[S1] = leq X0
X1`; Step Into shows `Rule: clause 9 leq.elpi:9 fires`, then the call of
the goal of the rule, `Call: #3 leq X0 X2`, at line 9 (the session of
[`tests/sessions.t`](tests/sessions.t)).

## The mapping

| DAP | elpi-debug |
|---|---|
| setBreakpoints (file, line) | `+ clause N`: N is the rule that holds the line; the run stops at the unify step of that rule (when it is selected for a call); on a CHR rule, at each attempt of the rule (`Rule: clause 9 leq.elpi:9 tried on [S1, S2]`) |
| setFunctionBreakpoints (name) | `+ P`: the run stops at the call port of each call of P (and at the resume of a goal of P woken by CHR) |
| configurationDone | `l` (leap to the first breakpoint), or with `stopOnEntry` a stop before the first event (shown at `queryPath`:`queryLine` when the launch gives them, e.g. the property of a counterexample; else with no line) |
| stepIn | `c` (creep: the next event) |
| next | `s` (skip the call) at the ports of a call; `c` at a step inside a call (unify, pi, `=>`, cut, delay), where skip would leave the call |
| stepOut | `o`: to the exit or fail port of the call whose body runs the event (at a port of a call: the call above) |
| continue | `l` (leap) |
| pause | the signal SIGUSR1: the run stops at its next event |
| restartFrame (call #N) | `r N`: retry call #N from its call port (bindings, local program and scope undone) |
| evaluate (debug console) | the command typed, its output as the answer |
| evaluate (watch) | from the description of the stop: a variable of the query by its source name (`L` of `append [1,2] [3] L`), its value now; a variable as elpi-debug names it (`X1`), its binding by the step of the stop (a unify step, an exit port), or `X1   (unbound)` when it is a logic variable of a goal of the stack; otherwise an error, "not in view at this stop" |
| stackTrace | the calls of the stop, the call in focus first, named `#N goal` (the first one prefixed by the port: `Call:`, `Unify:`, `Pi:`...).  A call at its own ports (call, exit, redo, fail), where it runs no clause, is at the goal it comes from, where it is written: the premise of its caller's clause, as a range (`line`, `column`, `endLine`, `endColumn`), so that the editor highlights that goal only; a call below it in the stack (its caller) is at the same goal, the call it made; the call in focus inside a clause (unify, pi, =>, cut) is at the line of that clause.  A call of the query or a woken goal, which has no premise, is where its caller is (the query: `queryPath`:`queryLine` when given); a call of the goal of a CHR rule is at the line of the rule; a call that runs a hypothetical clause has no source line.  At a stop at a CHR rule (its attempt, its outcome), the first frame is named by the event and is at the line of the rule |
| scopes | **Goal**: the goal, its arguments with their modes, and the bindings made by the step of the stop (`X0 := ...`, with the pruning, if any): at a unify step those of the head unification, at an exit port those of the whole call (when its call port was shown or stopped at); **Query**: the variables of the query by their source names, with their values at the stop (the same in every frame); **Local program (=>)**: the clauses added by `=>`, each with the call that added it; **Eigenvariables**: those in force, and for each logic variable of the goal the eigenvariables it may depend on; **Constraints**: the constraint store, the goals suspended by `declare_constraint`, most recent first, each named by its suspension (`[S2]`: `leq X1 X2`; the same in every frame) |
| stopped | reason `breakpoint`, `step`, `pause` or `entry`; the description says the port (`Call port`, `Unify step`, `Rule step`...), the text is the event |
| output | every line elpi-debug prints that is not for the adapter: the events shown, the prints of the program, the solutions, the explanation of a failure, the profile |
| exited, terminated | when elpi-debug ends |

A source line belongs to the last item of its file that starts at or
before it (a rule or a declaration, from the listing of elpi-debug); a
breakpoint is set when that item is a rule or a CHR rule (listed with the
rules, numbered after them), and VS Code moves it to the first line of
the rule.

## How it works

`elpi-debug -machine` ([`../debug/lib/machine.elpi`](../debug/lib/machine.elpi))
prints, besides its usual text, lines `@@elpi-debug {JSON}`: first the
listing of the program (its rules then its CHR rules, numbered, with file
and line; the lines of its declarations), then at each stop, in place of the prompt, the
description of the stop: its number, its reason, the event, the stack
(each call with the clause it runs, the premise it comes from and its
place, its arguments, the scope of its variables), the bindings of a unify step or of an exit port, the local
program, the eigenvariables, the variables of the query by their source
names with their values, the constraint store, and at a stop at a CHR
rule the place of the rule.  It waits at a stop `Start` before the first event, where
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

## The properties in the Test Explorer

The same extension shows the properties of [`elpi-check`](../check/README.md)
(`property "name" (pi X\ ...)` in a program) as tests of VS Code's Testing
API, module [`vscode/properties.js`](vscode/properties.js):

- **Discovery.**  When an `.elpi` file is opened, and again when it is
  saved, the extension runs `elpi-check -json -list FILE` (the checker's
  own analysis, not a regular expression: a property is found when Elpi
  compiles it), and the Test Explorer shows the file with one test per
  property; each property line gets the run buttons in its margin (the
  green triangle).  The description of a test lists its variables with
  their kind (`L : list int (generated), S : list int (computed)`).  A file
  without properties has no entry; a file that does not compile keeps its
  entries, marked with the error (the output channel "Elpi properties"
  has the messages and the command lines run).
- **Run** one property (its button, or its line in the Test Explorer:
  `elpi-check -json -p NAME FILE`), a file (one `elpi-check -json FILE`), or
  all (one per file).  A property that holds is green, its counts in the
  test output (`passed 100 tests, 0 discarded; average size of the values
  11`).  A failed one is red, with on its line the failure message: the
  shrunk counterexample with the computed values, the counts, the first
  counterexample and the replay goal.  `GAVE UP` (no test satisfied the
  premises) is a failure too.  A runtime error in a property stops
  elpi-check: that property is marked errored with the message, the ones
  after it in the file skipped.
- **Debug this counterexample.**  On a failure message (its button in the
  peek view, or its context menu), on a property in the Test Explorer (its
  context menu), or with the Debug profile (the debug button of a property
  runs it, then debugs its counterexample): VS Code starts the debugger
  (type `elpi`, as a launch configuration would) on the property's file
  with the **replay goal** of the shrunk counterexample, stopped on entry.
  The replay goal is the property's premises and conclusion with the
  generated values in place, `sort [0, 0] S, std.length [0, 0] N,
  std.length S M, N = M` for `sort-length` of
  [`../demo/lists.elpi`](../demo/lists.elpi); it fails, and one steps into
  why.  How it is made from the formula, generically, and when the
  computed values are pinned: [`../check/README.md`](../check/README.md),
  "Replaying a counterexample".  The debugger gets `-I elpi-tools/check/lib`
  (for `accumulate property`) and the `-I` of the setting
  `elpiTools.checkArgs`.

Settings: `elpiTools.checkPath` (elpi-check, by default the one built next
to the extension, else the PATH), `elpiTools.checkArgs` (more options,
e.g. `["-n", "1000"]`), `elpiTools.checkLibraryPath` (the directory of
`property.elpi` for the debugger).  elpi-check runs in the directory of
the file.

The modules: [`vscode/checkReport.js`](vscode/checkReport.js) reads the
report of `elpi-check -json` (one JSON object per line, see
[`../check/README.md`](../check/README.md), "The report for tools") and
computes what is shown and the debug configuration, without VS Code;
[`vscode/properties.js`](vscode/properties.js) is the Testing API part;
[`vscode/tools.js`](vscode/tools.js) finds the programs, for both tools.

### Manual check in VS Code (to be done by a person: not done)

**Not tested by clicking.**  What follows is what the code asks VS Code
to show; it was checked only in Node with a stand-in for the `vscode`
module ([`vscode/test`](vscode/test)), not in VS Code.

1. Install as above (`dune build`, the symbolic link), restart VS Code,
   open the folder `elpi-tools/demo`, open `lists.elpi`.
2. The Testing view (the flask in the activity bar) shows `lists.elpi` with
   `sort-sorted`, `sort-length`, `rev-agree`; lines 41, 44 and 48 have a run
   button in the margin.  If not: the output channel "Elpi properties"
   (View, Output) shows the command run and its error.
3. Click the run button of line 44 (`sort-length`): after about a second
   it turns red and the message on the line starts with `FAILED at test`,
   with `L = [0, 0]`, `S = [0]`, `N = 2`, `M = 1`, the counts `21 passed, 0
   discarded` and the replay goal.  Run the whole file (the button of
   `lists.elpi` in the Testing view): `sort-sorted` and `rev-agree` green,
   `sort-length` red with the same counterexample (a property draws its
   values from a random stream of its own, alone or in its file).
4. In the peek view of the failure, the button "Debug this counterexample"
   (also in the context menu of the message and of the test): the debugger
   starts on `sort [0, 0] S, std.length [0, 0] N, std.length S M, N = M`,
   stopped on entry.  Step Into: `Call: #1 sort [0, 0] X0`; Continue: the
   debug console shows `Deepest failure (depth 2): 0 < 0`, called from `#5
   insert 0 [0] [0, 0]`: no clause gives `[0, 0]`, since the clause of the
   bug (line 10) drops the second 0.
5. Open `lambda.elpi`: `preservation` and `unique-type`.  Run
   `preservation` with its debug button (the Debug profile): it fails with
   `M = app (lam (c0 \ c)) c`, `N = lam (c0 \ c)`, and the debugger starts
   at once on `of (app (lam (c0 \ c)) c) base, step (app (lam (c0 \ c)) c)
   N, N = lam (c0 \ c), of N base`, stopped on entry.  Step Into, then Step
   Over seven times: the last two stops are `Call: #8 of (lam c0 \ c) base`
   and `Fail: #8 of (lam c0 \ c) base`, the conclusion failing.
6. Edit a property (e.g. rename it) and save: the Testing view follows.
   Break the file (a syntax error) and save: its entry shows the error.

## Tests

`dune build @runtest` plays the scripts [`tests/*.dap`](tests) (one JSON
request per line, `{"await": E}` to wait for an event) with
`dap_replay` and compares the transcripts:

- [`tests/sessions.t`](tests/sessions.t): breakpoints on a clause and on
  a line without one, the stack, the scopes, step in, next, step out, the
  debug console, restart frame, continue (append); stop on entry, pi and
  `=>`, the scopes, a frame running a hypothetical clause, `f` from
  the console (λ-calculus); a function breakpoint met at a call and at
  the resume of a goal suspended by CHR; a breakpoint in the margin on a
  CHR rule: its attempt and outcome at the line of the rule, the scope
  Constraints, the goal of the rule (leq.elpi); the Query scope and watch
  expressions, the bindings of an exit port (append); a program that does
  not exist;
  a pause of a long run (only its reason is compared: where it stops
  depends on timing);
- [`tests/demo.t`](tests/demo.t): the seven configurations of the demo
  ([`../demo/.vscode/launch.json`](../demo/.vscode/launch.json)), below, and
  the two sessions that "Debug this counterexample" starts on the demo
  (the replay goals of `sort-length` and `preservation`, stepped).

When `node` is installed, it also runs the tests of the extension in Node
([`vscode/test`](vscode/test), `node --test`, Node 22 here):

- [`checkReport.test.js`](vscode/test/checkReport.test.js): the reading of
  the report (lines, chunks, events), the outcome of each property in a run
  (started, passed, failed, errored on a runtime error, skipped after it),
  the texts shown, the debug configuration of a counterexample;
- [`properties.test.js`](vscode/test/properties.test.js): `properties.js`
  with a stand-in for the module `vscode`
  ([`vscode-stand-in.js`](vscode/test/vscode-stand-in.js), which records
  the calls) and the real elpi-check on copies of the demo: the items
  discovered and their lines, a file without properties, a run of all and
  of one property, the failure message, "Debug this counterexample" from
  the message and on a property that holds, the Debug profile (the pinned
  replay goal of `preservation`), a runtime error.

Not tested: VS Code itself (clicking, what its panels show), the
extension inside VS Code (its real `vscode` module: the stand-in follows
the API documentation, it may differ in details such as the context keys
of the menus).

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
   runs a hypothesis), #2 and #1 on line 20 at the goal `pi x\ of x A =>
   of (F x) B`, highlighted (the premise their calls come from).
   Variables: Goal `X4 := X1`;
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
   below it, at `insert X S1 S` on line 16 (the goal that made #5,
   highlighted); Step Out: `Exit: #5 insert 0 [0] [0]`; Continue:
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
55 lines: a factory that starts `elpi-dap`, a provider that completes the
launch configurations) called from elpi-lang's `activate`; and a way to
find `elpi-dap` (a setting, as here, or the binaries of an opam package
`elpi-tools`).  The properties of elpi-check need, in the same way, the
`commands` and `menus` contributions and the settings `elpiTools.check*`,
[`vscode/properties.js`](vscode/properties.js) and
[`vscode/checkReport.js`](vscode/checkReport.js) (with
[`vscode/tools.js`](vscode/tools.js), shared), registered from `activate`.
The extension is one entry point ([`vscode/extension.js`](vscode/extension.js))
and one module per tool.

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
  variable different names in two places (two panels, or two lines; item
  2 of [`../debug/ELPI-FEATURE-REQUESTS.md`](../debug/ELPI-FEATURE-REQUESTS.md)).
- Under a directory named `_build` (as in dune's sandbox), Elpi's file
  resolver gives the program paths that do not exist, and breakpoints on
  lines are not found there (the tests run in a copy of their files).
- Inherited from elpi-debug: a cut through a variable, conjunctions of
  more than 16 goals, `=!=>`, CHR at depth 1 only (the rules run natively;
  their attempts, their goals and the store are shown: see
  [`../debug/README.md`](../debug/README.md), Limits).
- The properties: the Test Explorer lists those of the `.elpi` files
  opened in this session (and saved), not those of the files of the folder
  never opened.  Running one property (`-p`) gives other random values than
  running its file, hence possibly another counterexample.  The replay goal
  of a pinned counterexample (see [`../check/README.md`](../check/README.md))
  fails at the conclusion, but the debugger's explanation names the
  deepest failure, which may be in the backtracking of a premise (for
  `preservation`: `step c ..` at depth 2); stepping over the premises
  shows the conclusion failing (Manual check, step 5).  No time limit on elpi-check: a property that loops keeps its
  run going until it is cancelled (the stop button kills elpi-check).
