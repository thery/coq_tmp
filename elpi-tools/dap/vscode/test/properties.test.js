// Tests of properties.js (the Testing API part of the extension) in Node,
// with a stand-in for the module vscode (vscode-stand-in.js) and the real
// elpi-check on copies of the demo (demo/lists.elpi, demo/lambda.elpi) and of
// check/tests/crash.elpi.  What is tested: the items discovered, the
// states given to them by the runs, the failure messages, the debug
// configurations started.  Not tested: VS Code itself.
//
// elpi-check: $ELPI_CHECK (set by dune), else the one built next to the
// extension.
'use strict';

const test = require('node:test');
const assert = require('node:assert');
const Module = require('module');
const path = require('path');
const fs = require('fs');
const os = require('os');

// require('vscode') gives the stand-in
const standInPath = path.join(__dirname, 'vscode-stand-in.js');
const originalResolve = Module._resolveFilename;
Module._resolveFilename = function resolveVscode(request, ...rest) {
  return request === 'vscode' ? standInPath : originalResolve.call(this, request, ...rest);
};

const vscode = require('vscode');
const properties = require('../properties');
const extension = require('../extension');

const elpiTools = path.join(__dirname, '..', '..', '..');
const checkLibrary = path.join(elpiTools, 'check', 'lib');

// The programs are copied in a temporary directory: under _build (dune),
// Elpi's file resolver gives paths outside _build.
const work = fs.mkdtempSync(path.join(os.tmpdir(), 'elpi-tools-test-'));
function copied(file) {
  const copy = path.join(work, path.basename(file));
  fs.copyFileSync(file, copy);
  return copy;
}
const demo = work;
const lists = copied(path.join(elpiTools, 'demo', 'lists.elpi'));
const lambda = copied(path.join(elpiTools, 'demo', 'lambda.elpi'));
const crash = copied(path.join(elpiTools, 'check', 'tests', 'crash.elpi'));
const append = copied(path.join(elpiTools, 'dap', 'tests', 'append.elpi'));
test.after(() => fs.rmSync(work, { recursive: true, force: true }));

const { recorded, settings, neverCancelled } = vscode.standIn;
if (process.env.ELPI_CHECK) settings.checkPath = path.resolve(process.env.ELPI_CHECK);

const context = { subscriptions: [] };
const tests = properties.register(context);
const controller = vscode.standIn.controllers[0];

// [runProfile(kind)]: the run handler of the profile of that kind
function runProfile(kind) {
  return controller.profiles.find((profile) => profile.kind === kind).runHandler;
}

// [children(file)]: the property items of a file, by name
function children(file) {
  const items = new Map();
  controller.items.get(file).children.forEach((item) => items.set(item.label, item));
  return items;
}

// [lastRun()]: the last test run
function lastRun() {
  return recorded.runs[recorded.runs.length - 1];
}

test('discovery: a file item, a property item on each property line', async () => {
  await tests.discover(lists);
  const items = children(lists);
  assert.deepStrictEqual([...items.keys()], ['sort-sorted', 'sort-length', 'rev-agree']);
  assert.deepStrictEqual([...items.values()].map((item) => item.range.start.line), [40, 43, 47]);
  assert.strictEqual(items.get('sort-length').description,
                     'L : list int (generated), S : list int (computed), N : int (computed), M : int (computed)');
  assert.strictEqual(items.get('sort-length').uri.fsPath, lists);
});

test('a file without properties has no item', async () => {
  await tests.discover(append);
  assert.strictEqual(controller.items.get(append), undefined);
});

test('run all: one elpi-check on the file; passed, failed with the shrunk counterexample', async () => {
  await runProfile(vscode.TestRunProfileKind.Run)({ include: undefined, exclude: [] }, neverCancelled);
  const run = lastRun();
  const items = children(lists);
  assert.strictEqual(run.finalState(items.get('sort-sorted').id).state, 'passed');
  assert.strictEqual(run.finalState(items.get('rev-agree').id).state, 'passed');
  const failure = run.finalState(items.get('sort-length').id);
  assert.strictEqual(failure.state, 'failed');
  assert.match(failure.message.message, /^FAILED at test 23 \(22 passed, 0 discarded\); counterexample, shrunk in 1 steps:\n  L = \[0, 0\]\n  S = \[0\]/);
  assert.strictEqual(failure.message.contextValue, 'elpiCounterexample');
  assert.strictEqual(failure.message.location.range.start.line, 43);
  assert.match(run.output, /sort-sorted: passed 100 tests, 0 discarded/);
  assert.ok(run.ended);
});

test('run one property: elpi-check -p', async () => {
  const item = children(lists).get('sort-length');
  await runProfile(vscode.TestRunProfileKind.Run)({ include: [item], exclude: [] }, neverCancelled);
  const run = lastRun();
  assert.deepStrictEqual(run.states.map((s) => s.state), ['enqueued', 'started', 'failed']);
  assert.ok(tests.output.lines.includes(`elpi-check -json -p sort-length ${lists}`));
});

test('Debug this counterexample, from the failure message: the replay goal under the debugger', async () => {
  // the last run was -p sort-length: its random values differ from those of
  // the run of the whole file, and the shrinking stops at [2, 2] (a local
  // minimum: each element alone cannot shrink)
  const item = children(lists).get('sort-length');
  const message = lastRun().finalState(item.id).message;
  await recorded.commands.get('elpiTools.debugCounterexample')({ test: item, message });
  const configuration = recorded.debugSessions[recorded.debugSessions.length - 1];
  assert.deepStrictEqual(configuration, {
    type: 'elpi',
    request: 'launch',
    name: 'Counterexample of sort-length',
    program: lists,
    goal: 'sort [2, 2] S, std.length [2, 2] N, std.length S M, N = M',
    args: ['-I', checkLibrary],
    cwd: demo,
    stopOnEntry: true
  });
});

test('Debug this counterexample on a property that holds: a message, no debugging', async () => {
  const sessions = recorded.debugSessions.length;
  await recorded.commands.get('elpiTools.debugCounterexample')(children(lists).get('sort-sorted'));
  assert.strictEqual(recorded.debugSessions.length, sessions);
  assert.match(recorded.informationMessages[recorded.informationMessages.length - 1], /No counterexample for this property/);
});

test('the Debug profile: runs the property, then debugs its counterexample (pinned value)', async () => {
  await tests.discover(lambda);
  const item = children(lambda).get('preservation');
  await runProfile(vscode.TestRunProfileKind.Debug)({ include: [item], exclude: [] }, neverCancelled);
  assert.strictEqual(lastRun().finalState(item.id).state, 'failed');
  const configuration = recorded.debugSessions[recorded.debugSessions.length - 1];
  assert.strictEqual(configuration.goal,
                     'of (app (lam (c0 \\ c)) c) base, step (app (lam (c0 \\ c)) c) N, N = lam (c0 \\ c), of N base');
  assert.strictEqual(configuration.program, lambda);
});

test('a runtime error: the property is errored, the next one skipped', async () => {
  await tests.discover(crash);
  const fileItem = controller.items.get(crash);
  await runProfile(vscode.TestRunProfileKind.Run)({ include: [fileItem], exclude: [] }, neverCancelled);
  const run = lastRun();
  const items = children(crash);
  assert.strictEqual(run.finalState(items.get('fine').id).state, 'passed');
  const errored = run.finalState(items.get('crash').id);
  assert.strictEqual(errored.state, 'errored');
  assert.match(errored.message.message, /Evaluation of a non closed term/);
  assert.strictEqual(run.finalState(items.get('never-reached').id).state, 'skipped');
});

test('the entry point registers both tools', () => {
  const before = vscode.standIn.controllers.length;
  extension.activate({ subscriptions: [] });
  assert.strictEqual(vscode.standIn.controllers.length, before + 1);
  assert.ok(recorded.commands.has('elpiTools.debugCounterexample'));
});
