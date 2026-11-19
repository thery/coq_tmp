The demo of elpi-tools (../../demo, DEMO.md) in VS Code: the scripted DAP
sessions of the configurations of ../../demo/.vscode/launch.json, as VS
Code would play them when one clicks (README.md, "The demo in VS Code").
They run in a copy of the demo outside _build (with property.elpi, which
the demo accumulates; launch.json gives -I ../check/lib instead).

  $ here=$PWD; work=$(mktemp -d); cp ../../demo/*.elpi ../../check/lib/property.elpi *.dap "$work"; cd "$work"
  $ replay () { "$here"/dap_replay.exe elpi-dap "$1" | sed -E 's|"/[^"]*/([^/"]+[.]elpi)"|"\1"|g'; }

1. The wrong reduction: the breakpoint on line 26 stops at the unify step
of the wrong rule, after the first two answers were looked for:

  $ replay demo-step.dap
  # Configuration 1 of demo/.vscode/launch.json: all the reductions of (λx. c) c, a breakpoint on line 26 (the wrong rule).
  -> {"seq":1,"type":"request","command":"initialize","arguments":{"adapterID":"elpi"}}
  <- {"seq":1,"type":"response","request_seq":1,"success":true,"command":"initialize","body":{"supportsConfigurationDoneRequest":true,"supportsFunctionBreakpoints":true,"supportsRestartFrame":true,"supportsTerminateRequest":true,"supportsEvaluateForHovers":false,"supportsStepBack":false}}
  -> {"seq":2,"type":"request","command":"launch","arguments":{"program":"lambda.elpi","goal":"step (app (lam x\\ c) c) N","args":["-all"]}}
  <- {"seq":2,"type":"response","request_seq":2,"success":true,"command":"launch","body":null}
  <- {"seq":3,"type":"event","event":"initialized","body":null}
  -> {"seq":3,"type":"request","command":"setBreakpoints","arguments":{"source":{"path":"lambda.elpi"},"breakpoints":[{"line":26}]}}
  <- {"seq":4,"type":"response","request_seq":3,"success":true,"command":"setBreakpoints","body":{"breakpoints":[{"verified":true,"line":26}]}}
  -> {"seq":4,"type":"request","command":"configurationDone","arguments":{}}
  <- {"seq":5,"type":"response","request_seq":4,"success":true,"command":"configurationDone","body":null}
  <- {"seq":6,"type":"event","event":"output","body":{"category":"console","output":"Start: step (app (lam x\\ c) c) N   (running to the first breakpoint, or to the end)\n"}}
  <- {"seq":7,"type":"event","event":"output","body":{"category":"stdout","output":"Solution 1:\n"}}
  <- {"seq":8,"type":"event","event":"output","body":{"category":"stdout","output":"  N = c\n"}}
  <- {"seq":9,"type":"event","event":"output","body":{"category":"stdout","output":"Unify: #1 with lambda.elpi:26: step (app (lam c0 \\ c) c) (lam c0 \\ c)\n"}}
  <- {"seq":10,"type":"event","event":"output","body":{"category":"stdout","output":"      X0 := lam c0 \\ c\n"}}
  <- {"seq":11,"type":"event","event":"stopped","body":{"reason":"breakpoint","description":"Unify step","text":"Unify: #1 with lambda.elpi:26: step (app (lam c0 \\ c) c) (lam c0 \\ c)\n      X0 := lam c0 \\ c","threadId":1,"allThreadsStopped":true}}
  -> {"seq":5,"type":"request","command":"stackTrace","arguments":{"threadId":1}}
  <- {"seq":12,"type":"response","request_seq":5,"success":true,"command":"stackTrace","body":{"stackFrames":[{"name":"Unify: #1 step (app (lam c0 \\ c) c) (lam c0 \\ c)","id":1,"column":1,"source":{"name":"lambda.elpi","path":"lambda.elpi"},"line":26}],"totalFrames":1}}
  -> {"seq":6,"type":"request","command":"variables","arguments":{"variablesReference":1}}
  <- {"seq":13,"type":"response","request_seq":6,"success":true,"command":"variables","body":{"variables":[{"name":"goal","value":"step (app (lam c0 \\ c) c) (lam c0 \\ c)","variablesReference":0},{"name":"arg 1 (input)","value":"app (lam c0 \\ c) c","variablesReference":0},{"name":"arg 2 (output)","value":"lam c0 \\ c","variablesReference":0},{"name":"X0 :=","value":"lam c0 \\ c","variablesReference":0}]}}
  -> {"seq":7,"type":"request","command":"continue","arguments":{"threadId":1}}
  <- {"seq":14,"type":"response","request_seq":7,"success":true,"command":"continue","body":{"allThreadsContinued":true}}
  <- {"seq":15,"type":"event","event":"output","body":{"category":"stdout","output":"Solution 2:\n"}}
  <- {"seq":16,"type":"event","event":"output","body":{"category":"stdout","output":"  N = lam c0 \\ c\n"}}
  <- {"seq":17,"type":"event","event":"output","body":{"category":"stdout","output":"debug: no (more) solution.\n"}}
  <- {"seq":18,"type":"event","event":"output","body":{"category":"stdout","output":"Deepest failure (depth 2): #3 step c (X10 x#1)\n"}}
  <- {"seq":19,"type":"event","event":"output","body":{"category":"stdout","output":"  called from:\n"}}
  <- {"seq":20,"type":"event","event":"output","body":{"category":"stdout","output":"    #2 step (lam c1 \\ c) (lam X10)\n"}}
  <- {"seq":21,"type":"event","event":"output","body":{"category":"stdout","output":"    #1 step (app (lam c1 \\ c) c) (app (lam X10) c)\n"}}
  <- {"seq":22,"type":"event","event":"output","body":{"category":"stdout","output":"  clauses tried:\n"}}
  <- {"seq":23,"type":"event","event":"output","body":{"category":"stdout","output":"    lambda.elpi:24: step (app (lam X1) X2) (X1 X2)\n"}}
  <- {"seq":24,"type":"event","event":"output","body":{"category":"stdout","output":"        does not match: argument 1 (input): c vs app (lam X1) X2\n"}}
  <- {"seq":25,"type":"event","event":"output","body":{"category":"stdout","output":"    lambda.elpi:25: step (app X3 X4) (app X5 X4)\n"}}
  <- {"seq":26,"type":"event","event":"output","body":{"category":"stdout","output":"        does not match: argument 1 (input): c vs app X3 X4\n"}}
  <- {"seq":27,"type":"event","event":"output","body":{"category":"stdout","output":"    lambda.elpi:26: step (app X6 X7) X6\n"}}
  <- {"seq":28,"type":"event","event":"output","body":{"category":"stdout","output":"        does not match: argument 1 (input): c vs app X6 X7\n"}}
  <- {"seq":29,"type":"event","event":"output","body":{"category":"stdout","output":"    lambda.elpi:27: step (lam X8) (lam X9)\n"}}
  <- {"seq":30,"type":"event","event":"output","body":{"category":"stdout","output":"        does not match: argument 1 (input): c vs lam X8\n"}}
  <- {"seq":31,"type":"event","event":"exited","body":{"exitCode":0}}
  <- {"seq":32,"type":"event","event":"terminated","body":null}
  -> {"seq":8,"type":"request","command":"disconnect","arguments":{}}
  <- {"seq":33,"type":"response","request_seq":8,"success":true,"command":"disconnect","body":null}

2. Hypotheses and eigenvariables: at the call of x (#3), its unify with the
hypothesis added by #1; the scopes of the call:

  $ replay demo-typing.dap
  # Configuration 2: the typing of λx.λy.x, stopped on entry; step in to the unify of the call of x (#3) with a hypothesis, then the scopes.
  -> {"seq":1,"type":"request","command":"initialize","arguments":{"adapterID":"elpi"}}
  <- {"seq":1,"type":"response","request_seq":1,"success":true,"command":"initialize","body":{"supportsConfigurationDoneRequest":true,"supportsFunctionBreakpoints":true,"supportsRestartFrame":true,"supportsTerminateRequest":true,"supportsEvaluateForHovers":false,"supportsStepBack":false}}
  -> {"seq":2,"type":"request","command":"launch","arguments":{"program":"lambda.elpi","goal":"of (lam x\\ lam y\\ x) T","stopOnEntry":true}}
  <- {"seq":2,"type":"response","request_seq":2,"success":true,"command":"launch","body":null}
  <- {"seq":3,"type":"event","event":"initialized","body":null}
  -> {"seq":3,"type":"request","command":"configurationDone","arguments":{}}
  <- {"seq":4,"type":"response","request_seq":3,"success":true,"command":"configurationDone","body":null}
  <- {"seq":5,"type":"event","event":"output","body":{"category":"console","output":"Start: of (lam x\\ lam y\\ x) T   (stopped before the first call: F11 steps into it, F5 runs to a breakpoint or to the end)\n"}}
  <- {"seq":6,"type":"event","event":"stopped","body":{"reason":"entry","description":"Start step","text":"Start: the run is about to start","threadId":1,"allThreadsStopped":true}}
  -> {"seq":4,"type":"request","command":"stepIn","arguments":{"threadId":1}}
  <- {"seq":7,"type":"response","request_seq":4,"success":true,"command":"stepIn","body":null}
  <- {"seq":8,"type":"event","event":"output","body":{"category":"stdout","output":"Call: #1 of (lam c0 \\ lam c1 \\ c0) X0\n"}}
  <- {"seq":9,"type":"event","event":"stopped","body":{"reason":"step","description":"Call port","text":"Call: #1 of (lam c0 \\ lam c1 \\ c0) X0","threadId":1,"allThreadsStopped":true}}
  -> {"seq":5,"type":"request","command":"stepIn","arguments":{"threadId":1}}
  <- {"seq":10,"type":"response","request_seq":5,"success":true,"command":"stepIn","body":null}
  <- {"seq":11,"type":"event","event":"output","body":{"category":"stdout","output":"Unify: #1 with lambda.elpi:20: of (lam c0 \\ lam c1 \\ c0) (arr X1 X2)\n"}}
  <- {"seq":12,"type":"event","event":"output","body":{"category":"stdout","output":"      X0 := arr X1 X2\n"}}
  <- {"seq":13,"type":"event","event":"stopped","body":{"reason":"step","description":"Unify step","text":"Unify: #1 with lambda.elpi:20: of (lam c0 \\ lam c1 \\ c0) (arr X1 X2)\n      X0 := arr X1 X2","threadId":1,"allThreadsStopped":true}}
  -> {"seq":6,"type":"request","command":"stepIn","arguments":{"threadId":1}}
  <- {"seq":14,"type":"response","request_seq":6,"success":true,"command":"stepIn","body":null}
  <- {"seq":15,"type":"event","event":"output","body":{"category":"stdout","output":"  Pi: x#1 is a new eigenvariable; its scope: (of x#1 X1) ==> of (lam c1 \\ x#1) X2\n"}}
  <- {"seq":16,"type":"event","event":"stopped","body":{"reason":"step","description":"Pi step","text":"Pi: x#1 is a new eigenvariable; its scope: (of x#1 X1) ==> of (lam c1 \\ x#1) X2","threadId":1,"allThreadsStopped":true}}
  -> {"seq":7,"type":"request","command":"stepIn","arguments":{"threadId":1}}
  <- {"seq":17,"type":"response","request_seq":7,"success":true,"command":"stepIn","body":null}
  <- {"seq":18,"type":"event","event":"output","body":{"category":"stdout","output":"  Assume: of x#1 X1   (added to the local program, for of (lam c1 \\ x#1) X2 only)\n"}}
  <- {"seq":19,"type":"event","event":"stopped","body":{"reason":"step","description":"Assume step","text":"Assume: of x#1 X1   (added to the local program, for of (lam c1 \\ x#1) X2 only)","threadId":1,"allThreadsStopped":true}}
  -> {"seq":8,"type":"request","command":"stepIn","arguments":{"threadId":1}}
  <- {"seq":20,"type":"response","request_seq":8,"success":true,"command":"stepIn","body":null}
  <- {"seq":21,"type":"event","event":"output","body":{"category":"stdout","output":"  Call: #2 of (lam c1 \\ x#1) X2   (premise 1 of lambda.elpi:20)\n"}}
  <- {"seq":22,"type":"event","event":"stopped","body":{"reason":"step","description":"Call port","text":"Call: #2 of (lam c1 \\ x#1) X2   (premise 1 of lambda.elpi:20)","threadId":1,"allThreadsStopped":true}}
  -> {"seq":9,"type":"request","command":"stepIn","arguments":{"threadId":1}}
  <- {"seq":23,"type":"response","request_seq":9,"success":true,"command":"stepIn","body":null}
  <- {"seq":24,"type":"event","event":"output","body":{"category":"stdout","output":"  Unify: #2 with lambda.elpi:20: of (lam c1 \\ x#1) (arr X3 X4)\n"}}
  <- {"seq":25,"type":"event","event":"output","body":{"category":"stdout","output":"      X2 := arr X3 X4\n"}}
  <- {"seq":26,"type":"event","event":"stopped","body":{"reason":"step","description":"Unify step","text":"Unify: #2 with lambda.elpi:20: of (lam c1 \\ x#1) (arr X3 X4)\n      X2 := arr X3 X4","threadId":1,"allThreadsStopped":true}}
  -> {"seq":10,"type":"request","command":"stepIn","arguments":{"threadId":1}}
  <- {"seq":27,"type":"response","request_seq":10,"success":true,"command":"stepIn","body":null}
  <- {"seq":28,"type":"event","event":"output","body":{"category":"stdout","output":"    Pi: x#2 is a new eigenvariable; its scope: (of x#2 X3) ==> of x#1 X4\n"}}
  <- {"seq":29,"type":"event","event":"stopped","body":{"reason":"step","description":"Pi step","text":"Pi: x#2 is a new eigenvariable; its scope: (of x#2 X3) ==> of x#1 X4","threadId":1,"allThreadsStopped":true}}
  -> {"seq":11,"type":"request","command":"stepIn","arguments":{"threadId":1}}
  <- {"seq":30,"type":"response","request_seq":11,"success":true,"command":"stepIn","body":null}
  <- {"seq":31,"type":"event","event":"output","body":{"category":"stdout","output":"    Assume: of x#2 X3   (added to the local program, for of x#1 X4 only)\n"}}
  <- {"seq":32,"type":"event","event":"stopped","body":{"reason":"step","description":"Assume step","text":"Assume: of x#2 X3   (added to the local program, for of x#1 X4 only)","threadId":1,"allThreadsStopped":true}}
  -> {"seq":12,"type":"request","command":"stepIn","arguments":{"threadId":1}}
  <- {"seq":33,"type":"response","request_seq":12,"success":true,"command":"stepIn","body":null}
  <- {"seq":34,"type":"event","event":"output","body":{"category":"stdout","output":"    Call: #3 of x#1 X4   (premise 1 of lambda.elpi:20)\n"}}
  <- {"seq":35,"type":"event","event":"stopped","body":{"reason":"step","description":"Call port","text":"Call: #3 of x#1 X4   (premise 1 of lambda.elpi:20)","threadId":1,"allThreadsStopped":true}}
  -> {"seq":13,"type":"request","command":"stepIn","arguments":{"threadId":1}}
  <- {"seq":36,"type":"response","request_seq":13,"success":true,"command":"stepIn","body":null}
  <- {"seq":37,"type":"event","event":"output","body":{"category":"stdout","output":"    Unify: #3 with hypothesis added by #1: of x#1 X1\n"}}
  <- {"seq":38,"type":"event","event":"output","body":{"category":"stdout","output":"      X4 := X1\n"}}
  <- {"seq":39,"type":"event","event":"stopped","body":{"reason":"step","description":"Unify step","text":"Unify: #3 with hypothesis added by #1: of x#1 X1\n      X4 := X1","threadId":1,"allThreadsStopped":true}}
  -> {"seq":14,"type":"request","command":"stackTrace","arguments":{"threadId":1}}
  <- {"seq":40,"type":"response","request_seq":14,"success":true,"command":"stackTrace","body":{"stackFrames":[{"name":"Unify: #3 of x#1 X1   (hypothesis added by #1)","id":3,"column":1,"line":0},{"name":"#2 of (lam c2 \\ x#1) (arr X3 X1)","id":2,"column":25,"source":{"name":"lambda.elpi","path":"lambda.elpi"},"line":20,"endLine":20,"endColumn":51},{"name":"#1 of (lam c2 \\ lam c3 \\ c2) (arr X1 (arr X3 X1))","id":1,"column":25,"source":{"name":"lambda.elpi","path":"lambda.elpi"},"line":20,"endLine":20,"endColumn":51}],"totalFrames":3}}
  -> {"seq":15,"type":"request","command":"variables","arguments":{"variablesReference":1}}
  <- {"seq":41,"type":"response","request_seq":15,"success":true,"command":"variables","body":{"variables":[{"name":"goal","value":"of x#1 X1","variablesReference":0},{"name":"arg 1 (output)","value":"x#1","variablesReference":0},{"name":"arg 2 (output)","value":"X1","variablesReference":0},{"name":"X4 :=","value":"X1","variablesReference":0}]}}
  -> {"seq":16,"type":"request","command":"variables","arguments":{"variablesReference":3}}
  <- {"seq":42,"type":"response","request_seq":16,"success":true,"command":"variables","body":{"variables":[{"name":"of x#2 X3","value":"hypothesis added by #2","variablesReference":0},{"name":"of x#1 X1","value":"hypothesis added by #1","variablesReference":0}]}}
  -> {"seq":17,"type":"request","command":"variables","arguments":{"variablesReference":4}}
  <- {"seq":43,"type":"response","request_seq":17,"success":true,"command":"variables","body":{"variables":[{"name":"x#1","value":"eigenvariable in force","variablesReference":0},{"name":"x#2","value":"eigenvariable in force","variablesReference":0},{"name":"X1","value":"may depend on no eigenvariable","variablesReference":0}]}}
  -> {"seq":18,"type":"request","command":"continue","arguments":{"threadId":1}}
  <- {"seq":44,"type":"response","request_seq":18,"success":true,"command":"continue","body":{"allThreadsContinued":true}}
  <- {"seq":45,"type":"event","event":"output","body":{"category":"stdout","output":"Solution 1:\n"}}
  <- {"seq":46,"type":"event","event":"output","body":{"category":"stdout","output":"  T = arr X1 (arr X3 X1)\n"}}
  <- {"seq":47,"type":"event","event":"exited","body":{"exitCode":0}}
  <- {"seq":48,"type":"event","event":"terminated","body":null}
  -> {"seq":19,"type":"request","command":"disconnect","arguments":{}}
  <- {"seq":49,"type":"response","request_seq":19,"success":true,"command":"disconnect","body":null}

3. A failure: the explanation (the occurs check) in the output:

  $ replay demo-failure.dap
  # Configuration 3: self-application has no type; the explanation of the failure is printed at the end.
  -> {"seq":1,"type":"request","command":"initialize","arguments":{"adapterID":"elpi"}}
  <- {"seq":1,"type":"response","request_seq":1,"success":true,"command":"initialize","body":{"supportsConfigurationDoneRequest":true,"supportsFunctionBreakpoints":true,"supportsRestartFrame":true,"supportsTerminateRequest":true,"supportsEvaluateForHovers":false,"supportsStepBack":false}}
  -> {"seq":2,"type":"request","command":"launch","arguments":{"program":"lambda.elpi","goal":"of (lam x\\ app x x) T","stopOnEntry":true}}
  <- {"seq":2,"type":"response","request_seq":2,"success":true,"command":"launch","body":null}
  <- {"seq":3,"type":"event","event":"initialized","body":null}
  -> {"seq":3,"type":"request","command":"configurationDone","arguments":{}}
  <- {"seq":4,"type":"response","request_seq":3,"success":true,"command":"configurationDone","body":null}
  <- {"seq":5,"type":"event","event":"output","body":{"category":"console","output":"Start: of (lam x\\ app x x) T   (stopped before the first call: F11 steps into it, F5 runs to a breakpoint or to the end)\n"}}
  <- {"seq":6,"type":"event","event":"stopped","body":{"reason":"entry","description":"Start step","text":"Start: the run is about to start","threadId":1,"allThreadsStopped":true}}
  -> {"seq":4,"type":"request","command":"continue","arguments":{"threadId":1}}
  <- {"seq":7,"type":"response","request_seq":4,"success":true,"command":"continue","body":{"allThreadsContinued":true}}
  <- {"seq":8,"type":"event","event":"output","body":{"category":"stdout","output":"debug: no (more) solution.\n"}}
  <- {"seq":9,"type":"event","event":"output","body":{"category":"stdout","output":"Deepest failure (depth 2): #4 of x#1 X1\n"}}
  <- {"seq":10,"type":"event","event":"output","body":{"category":"stdout","output":"  called from:\n"}}
  <- {"seq":11,"type":"event","event":"output","body":{"category":"stdout","output":"    #2 of (app x#1 x#1) X2\n"}}
  <- {"seq":12,"type":"event","event":"output","body":{"category":"stdout","output":"    #1 of (lam c1 \\ app c1 c1) (arr (arr X1 X2) X2)\n"}}
  <- {"seq":13,"type":"event","event":"output","body":{"category":"stdout","output":"  clauses tried:\n"}}
  <- {"seq":14,"type":"event","event":"output","body":{"category":"stdout","output":"    hypothesis added by #1: of x#1 (arr X1 X2)\n"}}
  <- {"seq":15,"type":"event","event":"output","body":{"category":"stdout","output":"        does not match: argument 2 (output): X1 vs arr X1 X2 (occurs check: X1 occurs in arr X1 X2)\n"}}
  <- {"seq":16,"type":"event","event":"output","body":{"category":"stdout","output":"    lambda.elpi:18: of c base\n"}}
  <- {"seq":17,"type":"event","event":"output","body":{"category":"stdout","output":"        does not match: argument 1 (output): x#1 vs c\n"}}
  <- {"seq":18,"type":"event","event":"output","body":{"category":"stdout","output":"    lambda.elpi:19: of (app X3 X4) X5\n"}}
  <- {"seq":19,"type":"event","event":"output","body":{"category":"stdout","output":"        does not match: argument 1 (output): x#1 vs app X3 X4\n"}}
  <- {"seq":20,"type":"event","event":"output","body":{"category":"stdout","output":"    lambda.elpi:20: of (lam X6) (arr X7 X8)\n"}}
  <- {"seq":21,"type":"event","event":"output","body":{"category":"stdout","output":"        does not match: argument 1 (output): x#1 vs lam X6\n"}}
  <- {"seq":22,"type":"event","event":"output","body":{"category":"stdout","output":"No solution.\n"}}
  <- {"seq":23,"type":"event","event":"exited","body":{"exitCode":0}}
  <- {"seq":24,"type":"event","event":"terminated","body":null}
  -> {"seq":5,"type":"request","command":"disconnect","arguments":{}}
  <- {"seq":25,"type":"response","request_seq":5,"success":true,"command":"disconnect","body":null}

4. A predicate defined nowhere: the function breakpoint stops at its call;
one step in shows its fail port:

  $ replay demo-nowhere.dap
  # Configuration 4, with a function breakpoint on positive (declared, defined nowhere): its call, then its fail.
  -> {"seq":1,"type":"request","command":"initialize","arguments":{"adapterID":"elpi"}}
  <- {"seq":1,"type":"response","request_seq":1,"success":true,"command":"initialize","body":{"supportsConfigurationDoneRequest":true,"supportsFunctionBreakpoints":true,"supportsRestartFrame":true,"supportsTerminateRequest":true,"supportsEvaluateForHovers":false,"supportsStepBack":false}}
  -> {"seq":2,"type":"request","command":"launch","arguments":{"program":"nowhere.elpi","goal":"check [1,2]"}}
  <- {"seq":2,"type":"response","request_seq":2,"success":true,"command":"launch","body":null}
  <- {"seq":3,"type":"event","event":"initialized","body":null}
  -> {"seq":3,"type":"request","command":"setFunctionBreakpoints","arguments":{"breakpoints":[{"name":"positive"}]}}
  <- {"seq":4,"type":"response","request_seq":3,"success":true,"command":"setFunctionBreakpoints","body":{"breakpoints":[{"verified":true,"message":"the program has no rule for positive"}]}}
  -> {"seq":4,"type":"request","command":"configurationDone","arguments":{}}
  <- {"seq":5,"type":"response","request_seq":4,"success":true,"command":"configurationDone","body":null}
  <- {"seq":6,"type":"event","event":"output","body":{"category":"console","output":"Start: check [1,2]   (running to the first breakpoint, or to the end)\n"}}
  <- {"seq":7,"type":"event","event":"output","body":{"category":"stdout","output":"  Call: #2 positive 1   (premise 1 of nowhere.elpi:4)\n"}}
  <- {"seq":8,"type":"event","event":"stopped","body":{"reason":"breakpoint","description":"Call port","text":"Call: #2 positive 1   (premise 1 of nowhere.elpi:4)","threadId":1,"allThreadsStopped":true}}
  -> {"seq":5,"type":"request","command":"stepIn","arguments":{"threadId":1}}
  <- {"seq":9,"type":"response","request_seq":5,"success":true,"command":"stepIn","body":null}
  <- {"seq":10,"type":"event","event":"output","body":{"category":"stdout","output":"  Fail: #2 positive 1\n"}}
  <- {"seq":11,"type":"event","event":"stopped","body":{"reason":"step","description":"Fail port","text":"Fail: #2 positive 1","threadId":1,"allThreadsStopped":true}}
  -> {"seq":6,"type":"request","command":"continue","arguments":{"threadId":1}}
  <- {"seq":12,"type":"response","request_seq":6,"success":true,"command":"continue","body":{"allThreadsContinued":true}}
  <- {"seq":13,"type":"event","event":"output","body":{"category":"stdout","output":"debug warning: positive has no clause at all (in the program or in the hypotheses in scope); its calls fail\n"}}
  <- {"seq":14,"type":"event","event":"output","body":{"category":"stdout","output":"debug: no (more) solution.\n"}}
  <- {"seq":15,"type":"event","event":"output","body":{"category":"stdout","output":"Deepest failure (depth 1): #2 positive 1\n"}}
  <- {"seq":16,"type":"event","event":"output","body":{"category":"stdout","output":"  called from:\n"}}
  <- {"seq":17,"type":"event","event":"output","body":{"category":"stdout","output":"    #1 check [1, 2]\n"}}
  <- {"seq":18,"type":"event","event":"output","body":{"category":"stdout","output":"  positive is declared but has no clause at all (in the program or in the hypotheses in scope)\n"}}
  <- {"seq":19,"type":"event","event":"output","body":{"category":"stdout","output":"No solution.\n"}}
  <- {"seq":20,"type":"event","event":"exited","body":{"exitCode":0}}
  <- {"seq":21,"type":"event","event":"terminated","body":null}
  -> {"seq":7,"type":"request","command":"disconnect","arguments":{}}
  <- {"seq":22,"type":"response","request_seq":7,"success":true,"command":"disconnect","body":null}

5. Sorting: the breakpoint on line 10 (the wrong clause); step out to the
exit of insert:

  $ replay demo-sort.dap
  # Configuration 5: sort [0,0] S, a breakpoint on line 10 (the wrong clause of insert); the stack shows the call of sort above.
  -> {"seq":1,"type":"request","command":"initialize","arguments":{"adapterID":"elpi"}}
  <- {"seq":1,"type":"response","request_seq":1,"success":true,"command":"initialize","body":{"supportsConfigurationDoneRequest":true,"supportsFunctionBreakpoints":true,"supportsRestartFrame":true,"supportsTerminateRequest":true,"supportsEvaluateForHovers":false,"supportsStepBack":false}}
  -> {"seq":2,"type":"request","command":"launch","arguments":{"program":"lists.elpi","goal":"sort [0,0] S"}}
  <- {"seq":2,"type":"response","request_seq":2,"success":true,"command":"launch","body":null}
  <- {"seq":3,"type":"event","event":"initialized","body":null}
  -> {"seq":3,"type":"request","command":"setBreakpoints","arguments":{"source":{"path":"lists.elpi"},"breakpoints":[{"line":10}]}}
  <- {"seq":4,"type":"response","request_seq":3,"success":true,"command":"setBreakpoints","body":{"breakpoints":[{"verified":true,"line":10}]}}
  -> {"seq":4,"type":"request","command":"configurationDone","arguments":{}}
  <- {"seq":5,"type":"response","request_seq":4,"success":true,"command":"configurationDone","body":null}
  <- {"seq":6,"type":"event","event":"output","body":{"category":"console","output":"Start: sort [0,0] S   (running to the first breakpoint, or to the end)\n"}}
  <- {"seq":7,"type":"event","event":"output","body":{"category":"stdout","output":"  Unify: #5 with lists.elpi:10: insert 0 [0] [0]\n"}}
  <- {"seq":8,"type":"event","event":"output","body":{"category":"stdout","output":"      X0 := [0]\n"}}
  <- {"seq":9,"type":"event","event":"stopped","body":{"reason":"breakpoint","description":"Unify step","text":"Unify: #5 with lists.elpi:10: insert 0 [0] [0]\n      X0 := [0]","threadId":1,"allThreadsStopped":true}}
  -> {"seq":5,"type":"request","command":"stackTrace","arguments":{"threadId":1}}
  <- {"seq":10,"type":"response","request_seq":5,"success":true,"command":"stackTrace","body":{"stackFrames":[{"name":"Unify: #5 insert 0 [0] [0]","id":5,"column":1,"source":{"name":"lists.elpi","path":"lists.elpi"},"line":10},{"name":"#1 sort [0, 0] [0]","id":1,"column":30,"source":{"name":"lists.elpi","path":"lists.elpi"},"line":16,"endLine":16,"endColumn":43}],"totalFrames":2}}
  -> {"seq":6,"type":"request","command":"variables","arguments":{"variablesReference":1}}
  <- {"seq":11,"type":"response","request_seq":6,"success":true,"command":"variables","body":{"variables":[{"name":"goal","value":"insert 0 [0] [0]","variablesReference":0},{"name":"arg 1 (input)","value":"0","variablesReference":0},{"name":"arg 2 (input)","value":"[0]","variablesReference":0},{"name":"arg 3 (output)","value":"[0]","variablesReference":0},{"name":"X0 :=","value":"[0]","variablesReference":0}]}}
  -> {"seq":7,"type":"request","command":"stepOut","arguments":{"threadId":1}}
  <- {"seq":12,"type":"response","request_seq":7,"success":true,"command":"stepOut","body":null}
  <- {"seq":13,"type":"event","event":"output","body":{"category":"stdout","output":"  Exit: #5 insert 0 [0] [0]\n"}}
  <- {"seq":14,"type":"event","event":"stopped","body":{"reason":"step","description":"Exit port","text":"Exit: #5 insert 0 [0] [0]","threadId":1,"allThreadsStopped":true}}
  -> {"seq":8,"type":"request","command":"continue","arguments":{"threadId":1}}
  <- {"seq":15,"type":"response","request_seq":8,"success":true,"command":"continue","body":{"allThreadsContinued":true}}
  <- {"seq":16,"type":"event","event":"output","body":{"category":"stdout","output":"Solution 1:\n"}}
  <- {"seq":17,"type":"event","event":"output","body":{"category":"stdout","output":"  S = [0]\n"}}
  <- {"seq":18,"type":"event","event":"exited","body":{"exitCode":0}}
  <- {"seq":19,"type":"event","event":"terminated","body":null}
  -> {"seq":9,"type":"request","command":"disconnect","arguments":{}}
  <- {"seq":20,"type":"response","request_seq":9,"success":true,"command":"disconnect","body":null}

6. Sorting: a failure to explain:

  $ replay demo-sort-fails.dap
  # Configuration 6: sort [0,0] [0,0] fails; the explanation of the failure is printed at the end.
  -> {"seq":1,"type":"request","command":"initialize","arguments":{"adapterID":"elpi"}}
  <- {"seq":1,"type":"response","request_seq":1,"success":true,"command":"initialize","body":{"supportsConfigurationDoneRequest":true,"supportsFunctionBreakpoints":true,"supportsRestartFrame":true,"supportsTerminateRequest":true,"supportsEvaluateForHovers":false,"supportsStepBack":false}}
  -> {"seq":2,"type":"request","command":"launch","arguments":{"program":"lists.elpi","goal":"sort [0,0] [0,0]"}}
  <- {"seq":2,"type":"response","request_seq":2,"success":true,"command":"launch","body":null}
  <- {"seq":3,"type":"event","event":"initialized","body":null}
  -> {"seq":3,"type":"request","command":"configurationDone","arguments":{}}
  <- {"seq":4,"type":"response","request_seq":3,"success":true,"command":"configurationDone","body":null}
  <- {"seq":5,"type":"event","event":"output","body":{"category":"console","output":"Start: sort [0,0] [0,0]   (running to the first breakpoint, or to the end)\n"}}
  <- {"seq":6,"type":"event","event":"output","body":{"category":"stdout","output":"debug: no (more) solution.\n"}}
  <- {"seq":7,"type":"event","event":"output","body":{"category":"stdout","output":"Deepest failure (depth 2): 0 < 0\n"}}
  <- {"seq":8,"type":"event","event":"output","body":{"category":"stdout","output":"  called from:\n"}}
  <- {"seq":9,"type":"event","event":"output","body":{"category":"stdout","output":"    #5 insert 0 [0] [0, 0]\n"}}
  <- {"seq":10,"type":"event","event":"output","body":{"category":"stdout","output":"    #1 sort [0, 0] [0, 0]\n"}}
  <- {"seq":11,"type":"event","event":"output","body":{"category":"stdout","output":"  a builtin (not a predicate of the program): it ran natively and failed\n"}}
  <- {"seq":12,"type":"event","event":"output","body":{"category":"stdout","output":"No solution.\n"}}
  <- {"seq":13,"type":"event","event":"exited","body":{"exitCode":0}}
  <- {"seq":14,"type":"event","event":"terminated","body":null}
  -> {"seq":4,"type":"request","command":"disconnect","arguments":{}}
  <- {"seq":15,"type":"response","request_seq":4,"success":true,"command":"disconnect","body":null}

7. The profile (the times, which vary, replaced by T):

  $ replay demo-profile.dap | sed -E 's/ +[0-9]+[.][0-9]+\\n/ T\\n/g'
  # Configuration 7 with a shorter list (std.iota 20): the profile is printed at the end.
  -> {"seq":1,"type":"request","command":"initialize","arguments":{"adapterID":"elpi"}}
  <- {"seq":1,"type":"response","request_seq":1,"success":true,"command":"initialize","body":{"supportsConfigurationDoneRequest":true,"supportsFunctionBreakpoints":true,"supportsRestartFrame":true,"supportsTerminateRequest":true,"supportsEvaluateForHovers":false,"supportsStepBack":false}}
  -> {"seq":2,"type":"request","command":"launch","arguments":{"program":"lists.elpi","goal":"std.iota 20 L, naive-rev L R1, rev L R2","args":["-profile"]}}
  <- {"seq":2,"type":"response","request_seq":2,"success":true,"command":"launch","body":null}
  <- {"seq":3,"type":"event","event":"initialized","body":null}
  -> {"seq":3,"type":"request","command":"configurationDone","arguments":{}}
  <- {"seq":4,"type":"response","request_seq":3,"success":true,"command":"configurationDone","body":null}
  <- {"seq":5,"type":"event","event":"output","body":{"category":"console","output":"Start: std.iota 20 L, naive-rev L R1, rev L R2   (running to the first breakpoint, or to the end)\n"}}
  <- {"seq":6,"type":"event","event":"output","body":{"category":"stdout","output":"Profile (ports per predicate; tries = clauses tried; self time):\n"}}
  <- {"seq":7,"type":"event","event":"output","body":{"category":"stdout","output":"  predicate                        calls   exits   redos   fails   tries   time (ms)\n"}}
  <- {"seq":8,"type":"event","event":"output","body":{"category":"stdout","output":"  (query)                              0       0       0       0       0 T\n"}}
  <- {"seq":9,"type":"event","event":"output","body":{"category":"stdout","output":"  append                             210     210       0       0     400 T\n"}}
  <- {"seq":10,"type":"event","event":"output","body":{"category":"stdout","output":"  naive-rev                           21      21       0       0      41 T\n"}}
  <- {"seq":11,"type":"event","event":"output","body":{"category":"stdout","output":"  rev                                  1       1       0       0       1 T\n"}}
  <- {"seq":12,"type":"event","event":"output","body":{"category":"stdout","output":"  rev-onto                            21      21       0       0      41 T\n"}}
  <- {"seq":13,"type":"event","event":"output","body":{"category":"stdout","output":"  std.iota (builtin)                   1       1       0       0       0 T\n"}}
  <- {"seq":14,"type":"event","event":"output","body":{"category":"stdout","output":"Solution 1:\n"}}
  <- {"seq":15,"type":"event","event":"output","body":{"category":"stdout","output":"  L = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]\n"}}
  <- {"seq":16,"type":"event","event":"output","body":{"category":"stdout","output":"  R1 = [19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]\n"}}
  <- {"seq":17,"type":"event","event":"output","body":{"category":"stdout","output":"  R2 = [19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]\n"}}
  <- {"seq":18,"type":"event","event":"exited","body":{"exitCode":0}}
  <- {"seq":19,"type":"event","event":"terminated","body":null}
  -> {"seq":4,"type":"request","command":"disconnect","arguments":{}}
  <- {"seq":20,"type":"response","request_seq":4,"success":true,"command":"disconnect","body":null}

8. Debug this counterexample (from the Test Explorer, see README.md): the
replay goal of a failed property, as the extension launches it (with
stopOnEntry), then the one of a property whose computed variable is
pinned:

  $ replay demo-counterexample.dap
  # Debug this counterexample (the Test Explorer, dap/vscode/properties.js): the replay goal of sort-length (demo/lists.elpi), stopped on entry; two steps, then continue: the explanation of the failure.
  -> {"seq":1,"type":"request","command":"initialize","arguments":{"adapterID":"elpi"}}
  <- {"seq":1,"type":"response","request_seq":1,"success":true,"command":"initialize","body":{"supportsConfigurationDoneRequest":true,"supportsFunctionBreakpoints":true,"supportsRestartFrame":true,"supportsTerminateRequest":true,"supportsEvaluateForHovers":false,"supportsStepBack":false}}
  -> {"seq":2,"type":"request","command":"launch","arguments":{"program":"lists.elpi","goal":"sort [0, 0] S, std.length [0, 0] N, std.length S M, N = M","stopOnEntry":true,"queryPath":"lists.elpi","queryLine":44}}
  <- {"seq":2,"type":"response","request_seq":2,"success":true,"command":"launch","body":null}
  <- {"seq":3,"type":"event","event":"initialized","body":null}
  -> {"seq":3,"type":"request","command":"configurationDone","arguments":{}}
  <- {"seq":4,"type":"response","request_seq":3,"success":true,"command":"configurationDone","body":null}
  <- {"seq":5,"type":"event","event":"output","body":{"category":"console","output":"Start: sort [0, 0] S, std.length [0, 0] N, std.length S M, N = M   (stopped before the first call: F11 steps into it, F5 runs to a breakpoint or to the end)\n"}}
  <- {"seq":6,"type":"event","event":"stopped","body":{"reason":"entry","description":"Start step","text":"Start: the run is about to start","threadId":1,"allThreadsStopped":true}}
  -> {"seq":4,"type":"request","command":"stackTrace","arguments":{"threadId":1}}
  <- {"seq":7,"type":"response","request_seq":4,"success":true,"command":"stackTrace","body":{"stackFrames":[{"name":"Start: (the query)","id":0,"column":1,"source":{"name":"lists.elpi","path":"lists.elpi"},"line":44}],"totalFrames":1}}
  -> {"seq":5,"type":"request","command":"stepIn","arguments":{"threadId":1}}
  <- {"seq":8,"type":"response","request_seq":5,"success":true,"command":"stepIn","body":null}
  <- {"seq":9,"type":"event","event":"output","body":{"category":"stdout","output":"Call: #1 sort [0, 0] X0\n"}}
  <- {"seq":10,"type":"event","event":"stopped","body":{"reason":"step","description":"Call port","text":"Call: #1 sort [0, 0] X0","threadId":1,"allThreadsStopped":true}}
  -> {"seq":6,"type":"request","command":"stepIn","arguments":{"threadId":1}}
  <- {"seq":11,"type":"response","request_seq":6,"success":true,"command":"stepIn","body":null}
  <- {"seq":12,"type":"event","event":"output","body":{"category":"stdout","output":"Unify: #1 with lists.elpi:16: sort [0, 0] X0\n"}}
  <- {"seq":13,"type":"event","event":"stopped","body":{"reason":"step","description":"Unify step","text":"Unify: #1 with lists.elpi:16: sort [0, 0] X0","threadId":1,"allThreadsStopped":true}}
  -> {"seq":7,"type":"request","command":"continue","arguments":{"threadId":1}}
  <- {"seq":14,"type":"response","request_seq":7,"success":true,"command":"continue","body":{"allThreadsContinued":true}}
  <- {"seq":15,"type":"event","event":"output","body":{"category":"stdout","output":"debug: no (more) solution.\n"}}
  <- {"seq":16,"type":"event","event":"output","body":{"category":"stdout","output":"Deepest failure (depth 2): 0 < 0\n"}}
  <- {"seq":17,"type":"event","event":"output","body":{"category":"stdout","output":"  called from:\n"}}
  <- {"seq":18,"type":"event","event":"output","body":{"category":"stdout","output":"    #5 insert 0 [0] [0, 0]\n"}}
  <- {"seq":19,"type":"event","event":"output","body":{"category":"stdout","output":"    #1 sort [0, 0] [0, 0]\n"}}
  <- {"seq":20,"type":"event","event":"output","body":{"category":"stdout","output":"  a builtin (not a predicate of the program): it ran natively and failed\n"}}
  <- {"seq":21,"type":"event","event":"output","body":{"category":"stdout","output":"No solution.\n"}}
  <- {"seq":22,"type":"event","event":"exited","body":{"exitCode":0}}
  <- {"seq":23,"type":"event","event":"terminated","body":null}
  -> {"seq":8,"type":"request","command":"disconnect","arguments":{}}
  <- {"seq":24,"type":"response","request_seq":8,"success":true,"command":"disconnect","body":null}

  $ replay demo-counterexample-pinned.dap
  # Debug this counterexample: the replay goal of preservation (demo/lambda.elpi), where N is pinned to the value of the counterexample (step has a right answer first).  Stopped on entry; Step Into, then Step Over 7 times: the right reduction, rejected by the pin, the wrong one, the conclusion that fails; continue: the explanation.
  -> {"seq":1,"type":"request","command":"initialize","arguments":{"adapterID":"elpi"}}
  <- {"seq":1,"type":"response","request_seq":1,"success":true,"command":"initialize","body":{"supportsConfigurationDoneRequest":true,"supportsFunctionBreakpoints":true,"supportsRestartFrame":true,"supportsTerminateRequest":true,"supportsEvaluateForHovers":false,"supportsStepBack":false}}
  -> {"seq":2,"type":"request","command":"launch","arguments":{"program":"lambda.elpi","goal":"of (app (lam (c0 \\ c)) c) base, step (app (lam (c0 \\ c)) c) N, N = lam (c0 \\ c), of N base","stopOnEntry":true}}
  <- {"seq":2,"type":"response","request_seq":2,"success":true,"command":"launch","body":null}
  <- {"seq":3,"type":"event","event":"initialized","body":null}
  -> {"seq":3,"type":"request","command":"configurationDone","arguments":{}}
  <- {"seq":4,"type":"response","request_seq":3,"success":true,"command":"configurationDone","body":null}
  <- {"seq":5,"type":"event","event":"output","body":{"category":"console","output":"Start: of (app (lam (c0 \\ c)) c) base, step (app (lam (c0 \\ c)) c) N, N = lam (c0 \\ c), of N base   (stopped before the first call: F11 steps into it, F5 runs to a breakpoint or to the end)\n"}}
  <- {"seq":6,"type":"event","event":"stopped","body":{"reason":"entry","description":"Start step","text":"Start: the run is about to start","threadId":1,"allThreadsStopped":true}}
  -> {"seq":4,"type":"request","command":"stepIn","arguments":{"threadId":1}}
  <- {"seq":7,"type":"response","request_seq":4,"success":true,"command":"stepIn","body":null}
  <- {"seq":8,"type":"event","event":"output","body":{"category":"stdout","output":"Call: #1 of (app (lam c0 \\ c) c) base\n"}}
  <- {"seq":9,"type":"event","event":"stopped","body":{"reason":"step","description":"Call port","text":"Call: #1 of (app (lam c0 \\ c) c) base","threadId":1,"allThreadsStopped":true}}
  -> {"seq":5,"type":"request","command":"next","arguments":{"threadId":1}}
  <- {"seq":10,"type":"response","request_seq":5,"success":true,"command":"next","body":null}
  <- {"seq":11,"type":"event","event":"output","body":{"category":"stdout","output":"Exit: #1 of (app (lam c0 \\ c) c) base\n"}}
  <- {"seq":12,"type":"event","event":"stopped","body":{"reason":"step","description":"Exit port","text":"Exit: #1 of (app (lam c0 \\ c) c) base","threadId":1,"allThreadsStopped":true}}
  -> {"seq":6,"type":"request","command":"next","arguments":{"threadId":1}}
  <- {"seq":13,"type":"response","request_seq":6,"success":true,"command":"next","body":null}
  <- {"seq":14,"type":"event","event":"output","body":{"category":"stdout","output":"Call: #5 step (app (lam c0 \\ c) c) X0\n"}}
  <- {"seq":15,"type":"event","event":"stopped","body":{"reason":"step","description":"Call port","text":"Call: #5 step (app (lam c0 \\ c) c) X0","threadId":1,"allThreadsStopped":true}}
  -> {"seq":7,"type":"request","command":"next","arguments":{"threadId":1}}
  <- {"seq":16,"type":"response","request_seq":7,"success":true,"command":"next","body":null}
  <- {"seq":17,"type":"event","event":"output","body":{"category":"stdout","output":"Exit: #5 step (app (lam c0 \\ c) c) c\n"}}
  <- {"seq":18,"type":"event","event":"output","body":{"category":"stdout","output":"      X0 := c\n"}}
  <- {"seq":19,"type":"event","event":"stopped","body":{"reason":"step","description":"Exit port","text":"Exit: #5 step (app (lam c0 \\ c) c) c\n      X0 := c","threadId":1,"allThreadsStopped":true}}
  -> {"seq":8,"type":"request","command":"next","arguments":{"threadId":1}}
  <- {"seq":20,"type":"response","request_seq":8,"success":true,"command":"next","body":null}
  <- {"seq":21,"type":"event","event":"output","body":{"category":"stdout","output":"Redo: #5 step (app (lam c0 \\ c) c) c\n"}}
  <- {"seq":22,"type":"event","event":"stopped","body":{"reason":"step","description":"Redo port","text":"Redo: #5 step (app (lam c0 \\ c) c) c","threadId":1,"allThreadsStopped":true}}
  -> {"seq":9,"type":"request","command":"next","arguments":{"threadId":1}}
  <- {"seq":23,"type":"response","request_seq":9,"success":true,"command":"next","body":null}
  <- {"seq":24,"type":"event","event":"output","body":{"category":"stdout","output":"Exit: #5 step (app (lam c0 \\ c) c) (lam c0 \\ c)\n"}}
  <- {"seq":25,"type":"event","event":"output","body":{"category":"stdout","output":"      X0 := lam c0 \\ c\n"}}
  <- {"seq":26,"type":"event","event":"stopped","body":{"reason":"step","description":"Exit port","text":"Exit: #5 step (app (lam c0 \\ c) c) (lam c0 \\ c)\n      X0 := lam c0 \\ c","threadId":1,"allThreadsStopped":true}}
  -> {"seq":10,"type":"request","command":"next","arguments":{"threadId":1}}
  <- {"seq":27,"type":"response","request_seq":10,"success":true,"command":"next","body":null}
  <- {"seq":28,"type":"event","event":"output","body":{"category":"stdout","output":"Call: #8 of (lam c0 \\ c) base\n"}}
  <- {"seq":29,"type":"event","event":"stopped","body":{"reason":"step","description":"Call port","text":"Call: #8 of (lam c0 \\ c) base","threadId":1,"allThreadsStopped":true}}
  -> {"seq":11,"type":"request","command":"next","arguments":{"threadId":1}}
  <- {"seq":30,"type":"response","request_seq":11,"success":true,"command":"next","body":null}
  <- {"seq":31,"type":"event","event":"output","body":{"category":"stdout","output":"Fail: #8 of (lam c0 \\ c) base\n"}}
  <- {"seq":32,"type":"event","event":"stopped","body":{"reason":"step","description":"Fail port","text":"Fail: #8 of (lam c0 \\ c) base","threadId":1,"allThreadsStopped":true}}
  -> {"seq":12,"type":"request","command":"continue","arguments":{"threadId":1}}
  <- {"seq":33,"type":"response","request_seq":12,"success":true,"command":"continue","body":{"allThreadsContinued":true}}
  <- {"seq":34,"type":"event","event":"output","body":{"category":"stdout","output":"debug: no (more) solution.\n"}}
  <- {"seq":35,"type":"event","event":"output","body":{"category":"stdout","output":"Deepest failure (depth 2): #7 step c (X10 x#2)\n"}}
  <- {"seq":36,"type":"event","event":"output","body":{"category":"stdout","output":"  called from:\n"}}
  <- {"seq":37,"type":"event","event":"output","body":{"category":"stdout","output":"    #6 step (lam c1 \\ c) (lam X10)\n"}}
  <- {"seq":38,"type":"event","event":"output","body":{"category":"stdout","output":"    #5 step (app (lam c1 \\ c) c) (app (lam X10) c)\n"}}
  <- {"seq":39,"type":"event","event":"output","body":{"category":"stdout","output":"  clauses tried:\n"}}
  <- {"seq":40,"type":"event","event":"output","body":{"category":"stdout","output":"    lambda.elpi:24: step (app (lam X1) X2) (X1 X2)\n"}}
  <- {"seq":41,"type":"event","event":"output","body":{"category":"stdout","output":"        does not match: argument 1 (input): c vs app (lam X1) X2\n"}}
  <- {"seq":42,"type":"event","event":"output","body":{"category":"stdout","output":"    lambda.elpi:25: step (app X3 X4) (app X5 X4)\n"}}
  <- {"seq":43,"type":"event","event":"output","body":{"category":"stdout","output":"        does not match: argument 1 (input): c vs app X3 X4\n"}}
  <- {"seq":44,"type":"event","event":"output","body":{"category":"stdout","output":"    lambda.elpi:26: step (app X6 X7) X6\n"}}
  <- {"seq":45,"type":"event","event":"output","body":{"category":"stdout","output":"        does not match: argument 1 (input): c vs app X6 X7\n"}}
  <- {"seq":46,"type":"event","event":"output","body":{"category":"stdout","output":"    lambda.elpi:27: step (lam X8) (lam X9)\n"}}
  <- {"seq":47,"type":"event","event":"output","body":{"category":"stdout","output":"        does not match: argument 1 (input): c vs lam X8\n"}}
  <- {"seq":48,"type":"event","event":"output","body":{"category":"stdout","output":"No solution.\n"}}
  <- {"seq":49,"type":"event","event":"exited","body":{"exitCode":0}}
  <- {"seq":50,"type":"event","event":"terminated","body":null}
  -> {"seq":13,"type":"request","command":"disconnect","arguments":{}}
  <- {"seq":51,"type":"response","request_seq":13,"success":true,"command":"disconnect","body":null}

  $ cd "$here"; rm -r "$work"
