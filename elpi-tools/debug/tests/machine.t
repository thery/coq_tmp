Option -machine, for a front end (such as the debug adapter ../../dap):
the listing of the program and, at each stop, a line "@@elpi-debug
{JSON}" in place of the prompt (lib/machine.elpi).  The run waits at a
stop "Start", where breakpoints can be set before the first event.

A breakpoint on the second clause of append (numbered 2 in the listing),
leap to it, step into the recursive call, remove the breakpoint, step out
(to the exit of the first call), retry the first call (r 1), then run to
the end (paths shown relative to the test directory):

  $ printf '+ clause 2\nl\nc\n- clause 2\no\nr 1\nn\n' | elpi-debug -machine append.elpi 'append [1,2] [3] L' | sed -E 's|"/[^"]*/([^/"]+[.]elpi)"|"\1"|g'
  @@elpi-debug {"event":"program","clauses":[{"clause":1,"predicate":"append","file":"append.elpi","line":5},{"clause":2,"predicate":"append","file":"append.elpi","line":6},{"clause":3,"predicate":"app","file":"append.elpi","line":10},{"clause":4,"predicate":"app","file":"append.elpi","line":11},{"clause":5,"predicate":"rev","file":"append.elpi","line":14},{"clause":6,"predicate":"rev","file":"append.elpi","line":15}],"declarations":[{"file":"append.elpi","line":4},{"file":"append.elpi","line":9},{"file":"append.elpi","line":13}]}
  @@elpi-debug {"event":"stop","stop":1,"reason":"start","port":"Start","text":"Start: the run is about to start","frames":[{"id":0,"goal":"(the query)","clause":null,"premise":null,"args":[],"scope":[]}],"bindings":[],"hyps":[],"eigenvariables":[],"query":[{"name":"L","value":"X0"}],"store":[],"rule":null}
    breakpoint on the clause at append.elpi:6
  @@elpi-debug {"event":"stop","stop":1,"reason":"start","port":"Start","text":"Start: the run is about to start","frames":[{"id":0,"goal":"(the query)","clause":null,"premise":null,"args":[],"scope":[]}],"bindings":[],"hyps":[],"eigenvariables":[],"query":[{"name":"L","value":"X0"}],"store":[],"rule":null}
  Unify: #1 with append.elpi:6: append [1, 2] [3] [1 | X1]
        X0 := [1 | X1]
  @@elpi-debug {"event":"stop","stop":2,"reason":"breakpoint","port":"Unify","text":"Unify: #1 with append.elpi:6: append [1, 2] [3] [1 | X1]\n      X0 := [1 | X1]","frames":[{"id":1,"goal":"append [1, 2] [3] [1 | X1]","clause":{"file":"append.elpi","line":6},"premise":null,"args":[{"mode":"input","value":"[1, 2]"},{"mode":"input","value":"[3]"},{"mode":"output","value":"[1 | X1]"}],"scope":[{"var":"X1","depends":[]}]}],"bindings":[{"var":"X0","value":"[1 | X1]","pruning":""}],"hyps":[],"eigenvariables":[],"query":[{"name":"L","value":"[1 | X1]"}],"store":[],"rule":null}
    Call: #2 append [2] [3] X1   (premise 1 of append.elpi:6)
  @@elpi-debug {"event":"stop","stop":3,"reason":"step","port":"Call","text":"Call: #2 append [2] [3] X1   (premise 1 of append.elpi:6)","frames":[{"id":2,"goal":"append [2] [3] X1","clause":null,"premise":{"index":1,"clause":{"file":"append.elpi","line":6},"place":{"file":"append.elpi","line":6,"column":24,"endLine":6,"endColumn":36}},"args":[{"mode":"input","value":"[2]"},{"mode":"input","value":"[3]"},{"mode":"output","value":"X1"}],"scope":[{"var":"X1","depends":[]}]},{"id":1,"goal":"append [1, 2] [3] [1 | X1]","clause":{"file":"append.elpi","line":6},"premise":null,"args":[{"mode":"input","value":"[1, 2]"},{"mode":"input","value":"[3]"},{"mode":"output","value":"[1 | X1]"}],"scope":[{"var":"X1","depends":[]}]}],"bindings":[],"hyps":[],"eigenvariables":[],"query":[{"name":"L","value":"[1 | X1]"}],"store":[],"rule":null}
    no breakpoint on the clause at append.elpi:6
  @@elpi-debug {"event":"stop","stop":3,"reason":"step","port":"Call","text":"Call: #2 append [2] [3] X1   (premise 1 of append.elpi:6)","frames":[{"id":2,"goal":"append [2] [3] X1","clause":null,"premise":{"index":1,"clause":{"file":"append.elpi","line":6},"place":{"file":"append.elpi","line":6,"column":24,"endLine":6,"endColumn":36}},"args":[{"mode":"input","value":"[2]"},{"mode":"input","value":"[3]"},{"mode":"output","value":"X1"}],"scope":[{"var":"X1","depends":[]}]},{"id":1,"goal":"append [1, 2] [3] [1 | X1]","clause":{"file":"append.elpi","line":6},"premise":null,"args":[{"mode":"input","value":"[1, 2]"},{"mode":"input","value":"[3]"},{"mode":"output","value":"[1 | X1]"}],"scope":[{"var":"X1","depends":[]}]}],"bindings":[],"hyps":[],"eigenvariables":[],"query":[{"name":"L","value":"[1 | X1]"}],"store":[],"rule":null}
  Exit: #1 append [1, 2] [3] [1, 2, 3]
  @@elpi-debug {"event":"stop","stop":4,"reason":"step","port":"Exit","text":"Exit: #1 append [1, 2] [3] [1, 2, 3]","frames":[{"id":1,"goal":"append [1, 2] [3] [1, 2, 3]","clause":null,"premise":null,"args":[{"mode":"input","value":"[1, 2]"},{"mode":"input","value":"[3]"},{"mode":"output","value":"[1, 2, 3]"}],"scope":[]}],"bindings":[],"hyps":[],"eigenvariables":[],"query":[{"name":"L","value":"[1, 2, 3]"}],"store":[],"rule":null}
      retry #1: back to its call port
  Call: #1 append [1, 2] [3] X0
  @@elpi-debug {"event":"stop","stop":5,"reason":"step","port":"Call","text":"Call: #1 append [1, 2] [3] X0","frames":[{"id":1,"goal":"append [1, 2] [3] X0","clause":null,"premise":null,"args":[{"mode":"input","value":"[1, 2]"},{"mode":"input","value":"[3]"},{"mode":"output","value":"X0"}],"scope":[{"var":"X0","depends":[]}]}],"bindings":[],"hyps":[],"eigenvariables":[],"query":[{"name":"L","value":"X0"}],"store":[],"rule":null}
  Solution 1:
    L = [1, 2, 3]

Hypotheses and eigenvariables in the description of a stop, at the
Assume step of the typing of λx.λy.x:

  $ printf 'c\nc\nc\nc\nc\nc\nc\nc\nc\nc\nn\n' | elpi-debug -machine lambda.elpi 'of (lam x\ lam y\ x) T' | grep '"port":"Assume"' | tail -1 | sed -E 's|"/[^"]*/([^/"]+[.]elpi)"|"\1"|g'
  @@elpi-debug {"event":"stop","stop":9,"reason":"step","port":"Assume","text":"Assume: of x#2 X3   (added to the local program, for of x#1 X4 only)","frames":[{"id":2,"goal":"of (lam c2 \\ x#1) (arr X3 X4)","clause":{"file":"lambda.elpi","line":14},"premise":{"index":1,"clause":{"file":"lambda.elpi","line":14},"place":{"file":"lambda.elpi","line":14,"column":24,"endLine":14,"endColumn":50}},"args":[{"mode":"input","value":"lam c2 \\ x#1"},{"mode":"output","value":"arr X3 X4"}],"scope":[{"var":"X3","depends":[]},{"var":"X4","depends":[]}]},{"id":1,"goal":"of (lam c2 \\ lam c3 \\ c2) (arr X1 (arr X3 X4))","clause":{"file":"lambda.elpi","line":14},"premise":null,"args":[{"mode":"input","value":"lam c2 \\ lam c3 \\ c2"},{"mode":"output","value":"arr X1 (arr X3 X4)"}],"scope":[{"var":"X1","depends":[]},{"var":"X3","depends":[]},{"var":"X4","depends":[]}]}],"bindings":[],"hyps":[{"clause":"of x#1 X1","origin":"hypothesis added by #1"}],"eigenvariables":["x#1","x#2"],"query":[{"name":"T","value":"arr X1 (arr X3 X4)"}],"store":[],"rule":null}

Without a stop asked, the machine-readable run gives the answers of the
real engine (the cut goes through the clause context that -machine adds):

  $ for g in 'first 1 [0,3,5] X' 'under-pi A' 'under-impl B' 'in-or C' 'not-mem 1 [1,2]'; do echo l | elpi-debug -machine -all -no-explain cut.elpi "$g" | grep -v '^@@'; done
  Solution 1:
    X = 3
  Solution 1:
    A = 1
  Solution 1:
    B = 1
  Solution 1:
    C = 1
  Solution 2:
    C = 20
  No solution.
