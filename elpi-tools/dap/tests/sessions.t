Scripted DAP sessions: dap_replay plays each script (*.dap) with elpi-dap,
as VS Code would, and prints the messages sent (->) and received (<-).
The paths of the files are shown without their directory.  (The sessions
run in a copy of this directory outside _build: there Elpi's resolver gives
the files paths that do not exist.)

  $ here=$PWD; work=$(mktemp -d); cp *.elpi *.dap "$work"; cd "$work"
  $ replay () { "$here"/dap_replay.exe elpi-dap "$1" | sed -E 's|"/[^"]*/([^/"]+[.]elpi)"|"\1"|g'; }

A breakpoint on a clause (line 6, the second clause of append) and one on
a line with no clause; the stack, the scopes, the variables; step in,
next, step out; a command in the debug console; restart a frame (retry);
continue to the end:

  $ replay append.dap
  # The client starts the adapter and launches append [1,2] [3] L.
  -> {"seq":1,"type":"request","command":"initialize","arguments":{"adapterID":"elpi","linesStartAt1":true,"columnsStartAt1":true}}
  <- {"seq":1,"type":"response","request_seq":1,"success":true,"command":"initialize","body":{"supportsConfigurationDoneRequest":true,"supportsFunctionBreakpoints":true,"supportsRestartFrame":true,"supportsTerminateRequest":true,"supportsEvaluateForHovers":false,"supportsStepBack":false}}
  -> {"seq":2,"type":"request","command":"launch","arguments":{"program":"append.elpi","goal":"append [1,2] [3] L"}}
  <- {"seq":2,"type":"response","request_seq":2,"success":true,"command":"launch","body":null}
  <- {"seq":3,"type":"event","event":"initialized","body":null}
  # A breakpoint on line 6 (the second clause of append), and one on a comment line before any clause.
  -> {"seq":3,"type":"request","command":"setBreakpoints","arguments":{"source":{"path":"append.elpi"},"breakpoints":[{"line":6},{"line":2}]}}
  <- {"seq":4,"type":"response","request_seq":3,"success":true,"command":"setBreakpoints","body":{"breakpoints":[{"verified":true,"line":6},{"verified":false,"message":"no clause at this line"}]}}
  -> {"seq":4,"type":"request","command":"configurationDone","arguments":{}}
  <- {"seq":5,"type":"response","request_seq":4,"success":true,"command":"configurationDone","body":null}
  <- {"seq":6,"type":"event","event":"output","body":{"category":"console","output":"Start: append [1,2] [3] L   (running to the first breakpoint, or to the end)\n"}}
  <- {"seq":7,"type":"event","event":"output","body":{"category":"stdout","output":"Unify: #1 with append.elpi:6: append [1, 2] [3] [1 | X1]\n"}}
  <- {"seq":8,"type":"event","event":"output","body":{"category":"stdout","output":"      X0 := [1 | X1]\n"}}
  <- {"seq":9,"type":"event","event":"stopped","body":{"reason":"breakpoint","description":"Unify step","text":"Unify: #1 with append.elpi:6: append [1, 2] [3] [1 | X1]\n      X0 := [1 | X1]","threadId":1,"allThreadsStopped":true}}
  -> {"seq":5,"type":"request","command":"threads","arguments":{}}
  <- {"seq":10,"type":"response","request_seq":5,"success":true,"command":"threads","body":{"threads":[{"id":1,"name":"elpi"}]}}
  -> {"seq":6,"type":"request","command":"stackTrace","arguments":{"threadId":1}}
  <- {"seq":11,"type":"response","request_seq":6,"success":true,"command":"stackTrace","body":{"stackFrames":[{"name":"Unify: #1 append [1, 2] [3] [1 | X1]","id":1,"column":1,"source":{"name":"append.elpi","path":"append.elpi"},"line":6}],"totalFrames":1}}
  -> {"seq":7,"type":"request","command":"scopes","arguments":{"frameId":1}}
  <- {"seq":12,"type":"response","request_seq":7,"success":true,"command":"scopes","body":{"scopes":[{"name":"Goal","presentationHint":"arguments","variablesReference":1,"expensive":false},{"name":"Query","presentationHint":"locals","variablesReference":2,"expensive":false},{"name":"Local program (=>)","presentationHint":"locals","variablesReference":3,"expensive":false},{"name":"Eigenvariables","presentationHint":"locals","variablesReference":4,"expensive":false}]}}
  -> {"seq":8,"type":"request","command":"variables","arguments":{"variablesReference":1}}
  <- {"seq":13,"type":"response","request_seq":8,"success":true,"command":"variables","body":{"variables":[{"name":"goal","value":"append [1, 2] [3] [1 | X1]","variablesReference":0},{"name":"arg 1 (input)","value":"[1, 2]","variablesReference":0},{"name":"arg 2 (input)","value":"[3]","variablesReference":0},{"name":"arg 3 (output)","value":"[1 | X1]","variablesReference":0},{"name":"X0 :=","value":"[1 | X1]","variablesReference":0}]}}
  # Step in: the call port of the recursive call.
  -> {"seq":9,"type":"request","command":"stepIn","arguments":{"threadId":1}}
  <- {"seq":14,"type":"response","request_seq":9,"success":true,"command":"stepIn","body":null}
  <- {"seq":15,"type":"event","event":"output","body":{"category":"stdout","output":"  Call: #2 append [2] [3] X1   (premise 1 of append.elpi:6)\n"}}
  <- {"seq":16,"type":"event","event":"stopped","body":{"reason":"step","description":"Call port","text":"Call: #2 append [2] [3] X1   (premise 1 of append.elpi:6)","threadId":1,"allThreadsStopped":true}}
  -> {"seq":10,"type":"request","command":"stackTrace","arguments":{"threadId":1}}
  <- {"seq":17,"type":"response","request_seq":10,"success":true,"command":"stackTrace","body":{"stackFrames":[{"name":"Call: #2 append [2] [3] X1","id":2,"column":25,"source":{"name":"append.elpi","path":"append.elpi"},"line":6,"endLine":6,"endColumn":37},{"name":"#1 append [1, 2] [3] [1 | X1]","id":1,"column":25,"source":{"name":"append.elpi","path":"append.elpi"},"line":6,"endLine":6,"endColumn":37}],"totalFrames":2}}
  # Remove the breakpoint, step over the recursive call: its exit port.
  -> {"seq":11,"type":"request","command":"setBreakpoints","arguments":{"source":{"path":"append.elpi"},"breakpoints":[]}}
  <- {"seq":18,"type":"response","request_seq":11,"success":true,"command":"setBreakpoints","body":{"breakpoints":[]}}
  -> {"seq":12,"type":"request","command":"next","arguments":{"threadId":1}}
  <- {"seq":19,"type":"response","request_seq":12,"success":true,"command":"next","body":null}
  <- {"seq":20,"type":"event","event":"output","body":{"category":"stdout","output":"  Exit: #2 append [2] [3] [2, 3]\n"}}
  <- {"seq":21,"type":"event","event":"output","body":{"category":"stdout","output":"      X1 := [2, 3]\n"}}
  <- {"seq":22,"type":"event","event":"stopped","body":{"reason":"step","description":"Exit port","text":"Exit: #2 append [2] [3] [2, 3]\n      X1 := [2, 3]","threadId":1,"allThreadsStopped":true}}
  -> {"seq":13,"type":"request","command":"stackTrace","arguments":{"threadId":1}}
  <- {"seq":23,"type":"response","request_seq":13,"success":true,"command":"stackTrace","body":{"stackFrames":[{"name":"Exit: #2 append [2] [3] [2, 3]","id":2,"column":25,"source":{"name":"append.elpi","path":"append.elpi"},"line":6,"endLine":6,"endColumn":37},{"name":"#1 append [1, 2] [3] [1, 2, 3]","id":1,"column":25,"source":{"name":"append.elpi","path":"append.elpi"},"line":6,"endLine":6,"endColumn":37}],"totalFrames":2}}
  # Step out: the exit of the first call.
  -> {"seq":14,"type":"request","command":"stepOut","arguments":{"threadId":1}}
  <- {"seq":24,"type":"response","request_seq":14,"success":true,"command":"stepOut","body":null}
  <- {"seq":25,"type":"event","event":"output","body":{"category":"stdout","output":"Exit: #1 append [1, 2] [3] [1, 2, 3]\n"}}
  <- {"seq":26,"type":"event","event":"stopped","body":{"reason":"step","description":"Exit port","text":"Exit: #1 append [1, 2] [3] [1, 2, 3]","threadId":1,"allThreadsStopped":true}}
  # A command of elpi-debug in the debug console.
  -> {"seq":15,"type":"request","command":"evaluate","arguments":{"expression":"g","context":"repl"}}
  <- {"seq":27,"type":"response","request_seq":15,"success":true,"command":"evaluate","body":{"result":"  called from:\n","variablesReference":0}}
  # Restart the first call (retry), then continue to the end.
  -> {"seq":16,"type":"request","command":"restartFrame","arguments":{"frameId":1}}
  <- {"seq":28,"type":"response","request_seq":16,"success":true,"command":"restartFrame","body":null}
  <- {"seq":29,"type":"event","event":"output","body":{"category":"stdout","output":"    retry #1: back to its call port\n"}}
  <- {"seq":30,"type":"event","event":"output","body":{"category":"stdout","output":"Call: #1 append [1, 2] [3] X0\n"}}
  <- {"seq":31,"type":"event","event":"stopped","body":{"reason":"step","description":"Call port","text":"Call: #1 append [1, 2] [3] X0","threadId":1,"allThreadsStopped":true}}
  -> {"seq":17,"type":"request","command":"continue","arguments":{"threadId":1}}
  <- {"seq":32,"type":"response","request_seq":17,"success":true,"command":"continue","body":{"allThreadsContinued":true}}
  <- {"seq":33,"type":"event","event":"output","body":{"category":"stdout","output":"Solution 1:\n"}}
  <- {"seq":34,"type":"event","event":"output","body":{"category":"stdout","output":"  L = [1, 2, 3]\n"}}
  <- {"seq":35,"type":"event","event":"exited","body":{"exitCode":0}}
  <- {"seq":36,"type":"event","event":"terminated","body":null}
  -> {"seq":18,"type":"request","command":"disconnect","arguments":{}}
  <- {"seq":37,"type":"response","request_seq":18,"success":true,"command":"disconnect","body":null}

Stop on entry; step through pi and => (the typing of λx.λy.x); the three
scopes of a call: the goal, the local program (with the call that added
each clause), the eigenvariables (and what each logic variable may depend
on); a frame running a hypothetical clause; f from the debug console:

  $ replay lambda.dap
  # Stop on entry (before the first event), then step into the typing of λx.λy.x.
  -> {"seq":1,"type":"request","command":"initialize","arguments":{"adapterID":"elpi"}}
  <- {"seq":1,"type":"response","request_seq":1,"success":true,"command":"initialize","body":{"supportsConfigurationDoneRequest":true,"supportsFunctionBreakpoints":true,"supportsRestartFrame":true,"supportsTerminateRequest":true,"supportsEvaluateForHovers":false,"supportsStepBack":false}}
  -> {"seq":2,"type":"request","command":"launch","arguments":{"program":"lambda.elpi","goal":"of (lam x\\ lam y\\ x) T","stopOnEntry":true}}
  <- {"seq":2,"type":"response","request_seq":2,"success":true,"command":"launch","body":null}
  <- {"seq":3,"type":"event","event":"initialized","body":null}
  -> {"seq":3,"type":"request","command":"configurationDone","arguments":{}}
  <- {"seq":4,"type":"response","request_seq":3,"success":true,"command":"configurationDone","body":null}
  <- {"seq":5,"type":"event","event":"output","body":{"category":"console","output":"Start: of (lam x\\ lam y\\ x) T   (stopped before the first call: F11 steps into it, F5 runs to a breakpoint or to the end)\n"}}
  <- {"seq":6,"type":"event","event":"stopped","body":{"reason":"entry","description":"Start step","text":"Start: the run is about to start","threadId":1,"allThreadsStopped":true}}
  -> {"seq":4,"type":"request","command":"stackTrace","arguments":{"threadId":1}}
  <- {"seq":7,"type":"response","request_seq":4,"success":true,"command":"stackTrace","body":{"stackFrames":[{"name":"Start: (the query)","id":0,"column":1,"line":0}],"totalFrames":1}}
  # Eight steps in: call, unify, pi, assume (call #1), call, unify, pi, assume (call #2).
  -> {"seq":5,"type":"request","command":"stepIn","arguments":{"threadId":1}}
  <- {"seq":8,"type":"response","request_seq":5,"success":true,"command":"stepIn","body":null}
  <- {"seq":9,"type":"event","event":"output","body":{"category":"stdout","output":"Call: #1 of (lam c0 \\ lam c1 \\ c0) X0\n"}}
  <- {"seq":10,"type":"event","event":"stopped","body":{"reason":"step","description":"Call port","text":"Call: #1 of (lam c0 \\ lam c1 \\ c0) X0","threadId":1,"allThreadsStopped":true}}
  -> {"seq":6,"type":"request","command":"stepIn","arguments":{"threadId":1}}
  <- {"seq":11,"type":"response","request_seq":6,"success":true,"command":"stepIn","body":null}
  <- {"seq":12,"type":"event","event":"output","body":{"category":"stdout","output":"Unify: #1 with lambda.elpi:14: of (lam c0 \\ lam c1 \\ c0) (arr X1 X2)\n"}}
  <- {"seq":13,"type":"event","event":"output","body":{"category":"stdout","output":"      X0 := arr X1 X2\n"}}
  <- {"seq":14,"type":"event","event":"stopped","body":{"reason":"step","description":"Unify step","text":"Unify: #1 with lambda.elpi:14: of (lam c0 \\ lam c1 \\ c0) (arr X1 X2)\n      X0 := arr X1 X2","threadId":1,"allThreadsStopped":true}}
  -> {"seq":7,"type":"request","command":"stepIn","arguments":{"threadId":1}}
  <- {"seq":15,"type":"response","request_seq":7,"success":true,"command":"stepIn","body":null}
  <- {"seq":16,"type":"event","event":"output","body":{"category":"stdout","output":"  Pi: x#1 is a new eigenvariable; its scope: (of x#1 X1) ==> of (lam c1 \\ x#1) X2\n"}}
  <- {"seq":17,"type":"event","event":"stopped","body":{"reason":"step","description":"Pi step","text":"Pi: x#1 is a new eigenvariable; its scope: (of x#1 X1) ==> of (lam c1 \\ x#1) X2","threadId":1,"allThreadsStopped":true}}
  -> {"seq":8,"type":"request","command":"stepIn","arguments":{"threadId":1}}
  <- {"seq":18,"type":"response","request_seq":8,"success":true,"command":"stepIn","body":null}
  <- {"seq":19,"type":"event","event":"output","body":{"category":"stdout","output":"  Assume: of x#1 X1   (added to the local program, for of (lam c1 \\ x#1) X2 only)\n"}}
  <- {"seq":20,"type":"event","event":"stopped","body":{"reason":"step","description":"Assume step","text":"Assume: of x#1 X1   (added to the local program, for of (lam c1 \\ x#1) X2 only)","threadId":1,"allThreadsStopped":true}}
  -> {"seq":9,"type":"request","command":"stepIn","arguments":{"threadId":1}}
  <- {"seq":21,"type":"response","request_seq":9,"success":true,"command":"stepIn","body":null}
  <- {"seq":22,"type":"event","event":"output","body":{"category":"stdout","output":"  Call: #2 of (lam c1 \\ x#1) X2   (premise 1 of lambda.elpi:14)\n"}}
  <- {"seq":23,"type":"event","event":"stopped","body":{"reason":"step","description":"Call port","text":"Call: #2 of (lam c1 \\ x#1) X2   (premise 1 of lambda.elpi:14)","threadId":1,"allThreadsStopped":true}}
  -> {"seq":10,"type":"request","command":"stepIn","arguments":{"threadId":1}}
  <- {"seq":24,"type":"response","request_seq":10,"success":true,"command":"stepIn","body":null}
  <- {"seq":25,"type":"event","event":"output","body":{"category":"stdout","output":"  Unify: #2 with lambda.elpi:14: of (lam c1 \\ x#1) (arr X3 X4)\n"}}
  <- {"seq":26,"type":"event","event":"output","body":{"category":"stdout","output":"      X2 := arr X3 X4\n"}}
  <- {"seq":27,"type":"event","event":"stopped","body":{"reason":"step","description":"Unify step","text":"Unify: #2 with lambda.elpi:14: of (lam c1 \\ x#1) (arr X3 X4)\n      X2 := arr X3 X4","threadId":1,"allThreadsStopped":true}}
  -> {"seq":11,"type":"request","command":"stepIn","arguments":{"threadId":1}}
  <- {"seq":28,"type":"response","request_seq":11,"success":true,"command":"stepIn","body":null}
  <- {"seq":29,"type":"event","event":"output","body":{"category":"stdout","output":"    Pi: x#2 is a new eigenvariable; its scope: (of x#2 X3) ==> of x#1 X4\n"}}
  <- {"seq":30,"type":"event","event":"stopped","body":{"reason":"step","description":"Pi step","text":"Pi: x#2 is a new eigenvariable; its scope: (of x#2 X3) ==> of x#1 X4","threadId":1,"allThreadsStopped":true}}
  -> {"seq":12,"type":"request","command":"stepIn","arguments":{"threadId":1}}
  <- {"seq":31,"type":"response","request_seq":12,"success":true,"command":"stepIn","body":null}
  <- {"seq":32,"type":"event","event":"output","body":{"category":"stdout","output":"    Assume: of x#2 X3   (added to the local program, for of x#1 X4 only)\n"}}
  <- {"seq":33,"type":"event","event":"stopped","body":{"reason":"step","description":"Assume step","text":"Assume: of x#2 X3   (added to the local program, for of x#1 X4 only)","threadId":1,"allThreadsStopped":true}}
  # The four scopes of the call #2: its goal, the query, the local program, the eigenvariables.
  -> {"seq":13,"type":"request","command":"scopes","arguments":{"frameId":2}}
  <- {"seq":34,"type":"response","request_seq":13,"success":true,"command":"scopes","body":{"scopes":[{"name":"Goal","presentationHint":"arguments","variablesReference":1,"expensive":false},{"name":"Query","presentationHint":"locals","variablesReference":2,"expensive":false},{"name":"Local program (=>)","presentationHint":"locals","variablesReference":3,"expensive":false},{"name":"Eigenvariables","presentationHint":"locals","variablesReference":4,"expensive":false}]}}
  -> {"seq":14,"type":"request","command":"variables","arguments":{"variablesReference":1}}
  <- {"seq":35,"type":"response","request_seq":14,"success":true,"command":"variables","body":{"variables":[{"name":"goal","value":"of (lam c2 \\ x#1) (arr X3 X4)","variablesReference":0},{"name":"arg 1 (input)","value":"lam c2 \\ x#1","variablesReference":0},{"name":"arg 2 (output)","value":"arr X3 X4","variablesReference":0}]}}
  -> {"seq":15,"type":"request","command":"variables","arguments":{"variablesReference":2}}
  <- {"seq":36,"type":"response","request_seq":15,"success":true,"command":"variables","body":{"variables":[{"name":"T","value":"arr X1 (arr X3 X4)","variablesReference":0}]}}
  -> {"seq":16,"type":"request","command":"variables","arguments":{"variablesReference":3}}
  <- {"seq":37,"type":"response","request_seq":16,"success":true,"command":"variables","body":{"variables":[{"name":"of x#1 X1","value":"hypothesis added by #1","variablesReference":0}]}}
  -> {"seq":17,"type":"request","command":"variables","arguments":{"variablesReference":4}}
  <- {"seq":38,"type":"response","request_seq":17,"success":true,"command":"variables","body":{"variables":[{"name":"x#1","value":"eigenvariable in force","variablesReference":0},{"name":"x#2","value":"eigenvariable in force","variablesReference":0},{"name":"X3","value":"may depend on no eigenvariable","variablesReference":0},{"name":"X4","value":"may depend on no eigenvariable","variablesReference":0}]}}
  # The same scopes for the call #1 (second in the stack: references 5 to 8): its eigenvariables.
  -> {"seq":18,"type":"request","command":"variables","arguments":{"variablesReference":8}}
  <- {"seq":39,"type":"response","request_seq":18,"success":true,"command":"variables","body":{"variables":[{"name":"x#1","value":"eigenvariable in force","variablesReference":0},{"name":"x#2","value":"eigenvariable in force","variablesReference":0},{"name":"X1","value":"may depend on no eigenvariable","variablesReference":0},{"name":"X3","value":"may depend on no eigenvariable","variablesReference":0},{"name":"X4","value":"may depend on no eigenvariable","variablesReference":0}]}}
  # Next at a step inside a call creeps: the call port of #3, then its unify with a hypothesis.
  -> {"seq":19,"type":"request","command":"next","arguments":{"threadId":1}}
  <- {"seq":40,"type":"response","request_seq":19,"success":true,"command":"next","body":null}
  <- {"seq":41,"type":"event","event":"output","body":{"category":"stdout","output":"    Call: #3 of x#1 X4   (premise 1 of lambda.elpi:14)\n"}}
  <- {"seq":42,"type":"event","event":"stopped","body":{"reason":"step","description":"Call port","text":"Call: #3 of x#1 X4   (premise 1 of lambda.elpi:14)","threadId":1,"allThreadsStopped":true}}
  -> {"seq":20,"type":"request","command":"stepIn","arguments":{"threadId":1}}
  <- {"seq":43,"type":"response","request_seq":20,"success":true,"command":"stepIn","body":null}
  <- {"seq":44,"type":"event","event":"output","body":{"category":"stdout","output":"    Unify: #3 with hypothesis added by #1: of x#1 X1\n"}}
  <- {"seq":45,"type":"event","event":"output","body":{"category":"stdout","output":"      X4 := X1\n"}}
  <- {"seq":46,"type":"event","event":"stopped","body":{"reason":"step","description":"Unify step","text":"Unify: #3 with hypothesis added by #1: of x#1 X1\n      X4 := X1","threadId":1,"allThreadsStopped":true}}
  -> {"seq":21,"type":"request","command":"stackTrace","arguments":{"threadId":1}}
  <- {"seq":47,"type":"response","request_seq":21,"success":true,"command":"stackTrace","body":{"stackFrames":[{"name":"Unify: #3 of x#1 X1   (hypothesis added by #1)","id":3,"column":1,"line":0},{"name":"#2 of (lam c2 \\ x#1) (arr X3 X1)","id":2,"column":25,"source":{"name":"lambda.elpi","path":"lambda.elpi"},"line":14,"endLine":14,"endColumn":51},{"name":"#1 of (lam c2 \\ lam c3 \\ c2) (arr X1 (arr X3 X1))","id":1,"column":25,"source":{"name":"lambda.elpi","path":"lambda.elpi"},"line":14,"endLine":14,"endColumn":51}],"totalFrames":3}}
  # Make the call #3 fail from the debug console (f): the run goes on.
  -> {"seq":22,"type":"request","command":"evaluate","arguments":{"expression":"f","context":"repl"}}
  <- {"seq":48,"type":"response","request_seq":22,"success":true,"command":"evaluate","body":{"result":"","variablesReference":0}}
  <- {"seq":49,"type":"event","event":"continued","body":{"threadId":1}}
  <- {"seq":50,"type":"event","event":"output","body":{"category":"stdout","output":"    Fail: #3 of x#1 X4\n"}}
  <- {"seq":51,"type":"event","event":"stopped","body":{"reason":"step","description":"Fail port","text":"Fail: #3 of x#1 X4","threadId":1,"allThreadsStopped":true}}
  -> {"seq":23,"type":"request","command":"disconnect","arguments":{}}
  <- {"seq":52,"type":"response","request_seq":23,"success":true,"command":"disconnect","body":null}

A function breakpoint, met at the call of even and at the resume of the
goal that CHR suspended:

  $ replay chr.dap
  # A breakpoint on the predicate even: its call, then the resume of the goal suspended by CHR.
  -> {"seq":1,"type":"request","command":"initialize","arguments":{"adapterID":"elpi"}}
  <- {"seq":1,"type":"response","request_seq":1,"success":true,"command":"initialize","body":{"supportsConfigurationDoneRequest":true,"supportsFunctionBreakpoints":true,"supportsRestartFrame":true,"supportsTerminateRequest":true,"supportsEvaluateForHovers":false,"supportsStepBack":false}}
  -> {"seq":2,"type":"request","command":"launch","arguments":{"program":"chr.elpi","goal":"double 3 Y"}}
  <- {"seq":2,"type":"response","request_seq":2,"success":true,"command":"launch","body":null}
  <- {"seq":3,"type":"event","event":"initialized","body":null}
  -> {"seq":3,"type":"request","command":"setFunctionBreakpoints","arguments":{"breakpoints":[{"name":"even"},{"name":"nowhere"}]}}
  <- {"seq":4,"type":"response","request_seq":3,"success":true,"command":"setFunctionBreakpoints","body":{"breakpoints":[{"verified":true},{"verified":true,"message":"the program has no rule for nowhere"}]}}
  -> {"seq":4,"type":"request","command":"configurationDone","arguments":{}}
  <- {"seq":5,"type":"response","request_seq":4,"success":true,"command":"configurationDone","body":null}
  <- {"seq":6,"type":"event","event":"output","body":{"category":"console","output":"Start: double 3 Y   (running to the first breakpoint, or to the end)\n"}}
  <- {"seq":7,"type":"event","event":"output","body":{"category":"stdout","output":"  Call: #2 even X0   (premise 1 of chr.elpi:18)\n"}}
  <- {"seq":8,"type":"event","event":"stopped","body":{"reason":"breakpoint","description":"Call port","text":"Call: #2 even X0   (premise 1 of chr.elpi:18)","threadId":1,"allThreadsStopped":true}}
  -> {"seq":5,"type":"request","command":"continue","arguments":{"threadId":1}}
  <- {"seq":9,"type":"response","request_seq":5,"success":true,"command":"continue","body":{"allThreadsContinued":true}}
  <- {"seq":10,"type":"event","event":"output","body":{"category":"stdout","output":"  Exit: #2 even X0\n"}}
  <- {"seq":11,"type":"event","event":"output","body":{"category":"stdout","output":"    Resume: [S1] #3 even 6\n"}}
  <- {"seq":12,"type":"event","event":"stopped","body":{"reason":"breakpoint","description":"Resume port","text":"Resume: [S1] #3 even 6","threadId":1,"allThreadsStopped":true}}
  -> {"seq":6,"type":"request","command":"stackTrace","arguments":{"threadId":1}}
  <- {"seq":13,"type":"response","request_seq":6,"success":true,"command":"stackTrace","body":{"stackFrames":[{"name":"Resume: #3 even 6","id":3,"column":1,"source":{"name":"chr.elpi","path":"chr.elpi"},"line":10},{"name":"#2 even 6","id":2,"column":1,"source":{"name":"chr.elpi","path":"chr.elpi"},"line":10},{"name":"#1 double 3 6","id":1,"column":15,"source":{"name":"chr.elpi","path":"chr.elpi"},"line":18,"endLine":18,"endColumn":21}],"totalFrames":3}}
  -> {"seq":7,"type":"request","command":"continue","arguments":{"threadId":1}}
  <- {"seq":14,"type":"response","request_seq":7,"success":true,"command":"continue","body":{"allThreadsContinued":true}}
  <- {"seq":15,"type":"event","event":"output","body":{"category":"stdout","output":"    Exit: [S1] #3 even 6\n"}}
  <- {"seq":16,"type":"event","event":"output","body":{"category":"stdout","output":"Solution 1:\n"}}
  <- {"seq":17,"type":"event","event":"output","body":{"category":"stdout","output":"  Y = 6\n"}}
  <- {"seq":18,"type":"event","event":"exited","body":{"exitCode":0}}
  <- {"seq":19,"type":"event","event":"terminated","body":null}
  -> {"seq":8,"type":"request","command":"disconnect","arguments":{}}
  <- {"seq":20,"type":"response","request_seq":8,"success":true,"command":"disconnect","body":null}

The scope Query (the variables of the query by their source names, with
their values at the stop) and watch expressions (a variable of the query
by its name, a variable X3 as elpi-debug names it); at the exit port of
a call seen at its call port, the bindings the whole call made:

  $ replay watch.dap
  # The Query scope and watch expressions: launch append [1,2] [3] L, stop at the unify step of line 6.
  -> {"seq":1,"type":"request","command":"initialize","arguments":{"adapterID":"elpi","linesStartAt1":true,"columnsStartAt1":true}}
  <- {"seq":1,"type":"response","request_seq":1,"success":true,"command":"initialize","body":{"supportsConfigurationDoneRequest":true,"supportsFunctionBreakpoints":true,"supportsRestartFrame":true,"supportsTerminateRequest":true,"supportsEvaluateForHovers":false,"supportsStepBack":false}}
  -> {"seq":2,"type":"request","command":"launch","arguments":{"program":"append.elpi","goal":"append [1,2] [3] L","stopOnEntry":true}}
  <- {"seq":2,"type":"response","request_seq":2,"success":true,"command":"launch","body":null}
  <- {"seq":3,"type":"event","event":"initialized","body":null}
  -> {"seq":3,"type":"request","command":"configurationDone","arguments":{}}
  <- {"seq":4,"type":"response","request_seq":3,"success":true,"command":"configurationDone","body":null}
  <- {"seq":5,"type":"event","event":"output","body":{"category":"console","output":"Start: append [1,2] [3] L   (stopped before the first call: F11 steps into it, F5 runs to a breakpoint or to the end)\n"}}
  <- {"seq":6,"type":"event","event":"stopped","body":{"reason":"entry","description":"Start step","text":"Start: the run is about to start","threadId":1,"allThreadsStopped":true}}
  # At the start, before any event: L is unbound.
  -> {"seq":4,"type":"request","command":"evaluate","arguments":{"expression":"L","context":"watch"}}
  <- {"seq":7,"type":"response","request_seq":4,"success":true,"command":"evaluate","body":{"result":"X0","variablesReference":0}}
  # Step in: the call port of #1, then its unify step.
  -> {"seq":5,"type":"request","command":"stepIn","arguments":{"threadId":1}}
  <- {"seq":8,"type":"response","request_seq":5,"success":true,"command":"stepIn","body":null}
  <- {"seq":9,"type":"event","event":"output","body":{"category":"stdout","output":"Call: #1 append [1, 2] [3] X0\n"}}
  <- {"seq":10,"type":"event","event":"stopped","body":{"reason":"step","description":"Call port","text":"Call: #1 append [1, 2] [3] X0","threadId":1,"allThreadsStopped":true}}
  -> {"seq":6,"type":"request","command":"stepIn","arguments":{"threadId":1}}
  <- {"seq":11,"type":"response","request_seq":6,"success":true,"command":"stepIn","body":null}
  <- {"seq":12,"type":"event","event":"output","body":{"category":"stdout","output":"Unify: #1 with append.elpi:6: append [1, 2] [3] [1 | X1]\n"}}
  <- {"seq":13,"type":"event","event":"output","body":{"category":"stdout","output":"      X0 := [1 | X1]\n"}}
  <- {"seq":14,"type":"event","event":"stopped","body":{"reason":"step","description":"Unify step","text":"Unify: #1 with append.elpi:6: append [1, 2] [3] [1 | X1]\n      X0 := [1 | X1]","threadId":1,"allThreadsStopped":true}}
  -> {"seq":7,"type":"request","command":"scopes","arguments":{"frameId":1}}
  <- {"seq":15,"type":"response","request_seq":7,"success":true,"command":"scopes","body":{"scopes":[{"name":"Goal","presentationHint":"arguments","variablesReference":1,"expensive":false},{"name":"Query","presentationHint":"locals","variablesReference":2,"expensive":false},{"name":"Local program (=>)","presentationHint":"locals","variablesReference":3,"expensive":false},{"name":"Eigenvariables","presentationHint":"locals","variablesReference":4,"expensive":false}]}}
  -> {"seq":8,"type":"request","command":"variables","arguments":{"variablesReference":2}}
  <- {"seq":16,"type":"response","request_seq":8,"success":true,"command":"variables","body":{"variables":[{"name":"L","value":"[1 | X1]","variablesReference":0}]}}
  # Watches: the query variable L, the variable X0 bound by this step, X1 of the goal, an unknown name.
  -> {"seq":9,"type":"request","command":"evaluate","arguments":{"expression":"L","context":"watch"}}
  <- {"seq":17,"type":"response","request_seq":9,"success":true,"command":"evaluate","body":{"result":"[1 | X1]","variablesReference":0}}
  -> {"seq":10,"type":"request","command":"evaluate","arguments":{"expression":"X0","context":"watch"}}
  <- {"seq":18,"type":"response","request_seq":10,"success":true,"command":"evaluate","body":{"result":"[1 | X1]","variablesReference":0}}
  -> {"seq":11,"type":"request","command":"evaluate","arguments":{"expression":"X1","context":"watch"}}
  <- {"seq":19,"type":"response","request_seq":11,"success":true,"command":"evaluate","body":{"result":"X1   (unbound)","variablesReference":0}}
  -> {"seq":12,"type":"request","command":"evaluate","arguments":{"expression":"Y","context":"watch"}}
  <- {"seq":20,"type":"response","request_seq":12,"success":false,"command":"evaluate","message":"Y: not in view at this stop (not a variable of the query, nor of a goal of the stack)","body":{"error":{"id":1,"format":"Y: not in view at this stop (not a variable of the query, nor of a goal of the stack)"}}}
  # Step out to the exit of #1: the bindings the whole call made, and L again.
  -> {"seq":13,"type":"request","command":"stepOut","arguments":{"threadId":1}}
  <- {"seq":21,"type":"response","request_seq":13,"success":true,"command":"stepOut","body":null}
  <- {"seq":22,"type":"event","event":"output","body":{"category":"stdout","output":"Exit: #1 append [1, 2] [3] [1, 2, 3]\n"}}
  <- {"seq":23,"type":"event","event":"output","body":{"category":"stdout","output":"      X0 := [1, 2, 3]\n"}}
  <- {"seq":24,"type":"event","event":"stopped","body":{"reason":"step","description":"Exit port","text":"Exit: #1 append [1, 2] [3] [1, 2, 3]\n      X0 := [1, 2, 3]","threadId":1,"allThreadsStopped":true}}
  -> {"seq":14,"type":"request","command":"variables","arguments":{"variablesReference":1}}
  <- {"seq":25,"type":"response","request_seq":14,"success":true,"command":"variables","body":{"variables":[{"name":"goal","value":"append [1, 2] [3] [1, 2, 3]","variablesReference":0},{"name":"arg 1 (input)","value":"[1, 2]","variablesReference":0},{"name":"arg 2 (input)","value":"[3]","variablesReference":0},{"name":"arg 3 (output)","value":"[1, 2, 3]","variablesReference":0},{"name":"X0 :=","value":"[1, 2, 3]","variablesReference":0}]}}
  -> {"seq":15,"type":"request","command":"evaluate","arguments":{"expression":"L","context":"watch"}}
  <- {"seq":26,"type":"response","request_seq":15,"success":true,"command":"evaluate","body":{"result":"[1, 2, 3]","variablesReference":0}}
  -> {"seq":16,"type":"request","command":"evaluate","arguments":{"expression":"X0","context":"watch"}}
  <- {"seq":27,"type":"response","request_seq":16,"success":true,"command":"evaluate","body":{"result":"[1, 2, 3]","variablesReference":0}}
  -> {"seq":17,"type":"request","command":"continue","arguments":{"threadId":1}}
  <- {"seq":28,"type":"response","request_seq":17,"success":true,"command":"continue","body":{"allThreadsContinued":true}}
  <- {"seq":29,"type":"event","event":"output","body":{"category":"stdout","output":"Solution 1:\n"}}
  <- {"seq":30,"type":"event","event":"output","body":{"category":"stdout","output":"  L = [1, 2, 3]\n"}}
  <- {"seq":31,"type":"event","event":"exited","body":{"exitCode":0}}
  <- {"seq":32,"type":"event","event":"terminated","body":null}
  -> {"seq":18,"type":"request","command":"disconnect","arguments":{}}
  <- {"seq":33,"type":"response","request_seq":18,"success":true,"command":"disconnect","body":null}

A program that does not exist: launch fails, the session ends:

  $ replay errors.dap
  # A program that does not exist: launch fails, the session ends.
  -> {"seq":1,"type":"request","command":"initialize","arguments":{"adapterID":"elpi"}}
  <- {"seq":1,"type":"response","request_seq":1,"success":true,"command":"initialize","body":{"supportsConfigurationDoneRequest":true,"supportsFunctionBreakpoints":true,"supportsRestartFrame":true,"supportsTerminateRequest":true,"supportsEvaluateForHovers":false,"supportsStepBack":false}}
  -> {"seq":2,"type":"request","command":"launch","arguments":{"program":"missing.elpi","goal":"main"}}
  <- {"seq":2,"type":"event","event":"output","body":{"category":"stderr","output":"elpi-debug: no file missing.elpi\n"}}
  <- {"seq":3,"type":"response","request_seq":2,"success":false,"command":"launch","message":"elpi-debug stopped before the start of the run:\nelpi-debug: no file missing.elpi\n","body":{"error":{"id":1,"format":"elpi-debug stopped before the start of the run:\nelpi-debug: no file missing.elpi\n"}}}
  <- {"seq":4,"type":"event","event":"exited","body":{"exitCode":2}}
  <- {"seq":5,"type":"event","event":"terminated","body":null}
  -> {"seq":3,"type":"request","command":"disconnect","arguments":{}}
  <- {"seq":6,"type":"response","request_seq":3,"success":true,"command":"disconnect","body":null}

Pause a long run (where it stops depends on timing: only the reason is
shown):

  $ "$here"/dap_replay.exe elpi-dap pause.dap | grep -o '"event":"stopped","body":{"reason":"[a-z]*"'
  "event":"stopped","body":{"reason":"pause"
  $ cd "$here"; rm -r "$work"
