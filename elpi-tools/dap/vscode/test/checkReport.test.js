// Tests of checkReport.js (the reading of elpi-check -json), in Node
// without VS Code: node --test (run by dune build @runtest, see dune).
// The report lines are those of elpi-check on demo/lists.elpi and on
// check/tests/crash.elpi (check/tests/json.t), the paths shortened.
'use strict';

const test = require('node:test');
const assert = require('node:assert');
const report = require('../checkReport');

const lists = '/demo/lists.elpi';

const sortLengthProperty = `{"event": "property", "name": "sort-length", "file": "${lists}", "line": 44, "variables": [{"name": "L", "type": "list int", "kind": "generated"}, {"name": "S", "type": "list int", "kind": "computed"}, {"name": "N", "type": "int", "kind": "computed"}, {"name": "M", "type": "int", "kind": "computed"}]}`;
const sortLengthResult = `{"event": "result", "name": "sort-length", "file": "${lists}", "line": 44, "status": "failed", "passed": 22, "discarded": 0, "failed-at-test": 23, "first": [{"name": "L", "value": "[-4, 0, 0]"}, {"name": "S", "value": "[-4, 0]"}, {"name": "N", "value": "3"}, {"name": "M", "value": "2"}], "shrunk": [{"name": "L", "value": "[0, 0]"}, {"name": "S", "value": "[0]"}, {"name": "N", "value": "2"}, {"name": "M", "value": "1"}], "shrink-steps": 1, "replay": "sort [0, 0] S, std.length [0, 0] N, std.length S M, N = M"}`;
const sortSortedProperty = `{"event": "property", "name": "sort-sorted", "file": "${lists}", "line": 41, "variables": [{"name": "L", "type": "list int", "kind": "generated"}, {"name": "S", "type": "list int", "kind": "computed"}]}`;
const sortSortedResult = `{"event": "result", "name": "sort-sorted", "file": "${lists}", "line": 41, "status": "ok", "passed": 100, "discarded": 0, "average-size": 11}`;
const revAgreeProperty = `{"event": "property", "name": "rev-agree", "file": "${lists}", "line": 48, "variables": []}`;
const summary = '{"event": "summary", "holds": 2, "properties": 3}';

const property = (name, line) => ({ name, file: lists, line, variables: [] });

test('a line of the report is an event; another line is not', () => {
  assert.deepStrictEqual(report.parseReportLine(summary), { event: 'summary', holds: 2, properties: 3 });
  assert.strictEqual(report.parseReportLine('  OK: a print of the program'), null);
  assert.strictEqual(report.parseReportLine('{not json'), null);
  assert.strictEqual(report.parseReportLine('{"no": "event"}'), null);
});

test('the output is split into lines across chunks', () => {
  const splitter = new report.LineSplitter();
  assert.deepStrictEqual(splitter.push('{"event": "sum'), []);
  assert.deepStrictEqual(splitter.push('mary"}\n{"a"'), ['{"event": "summary"}']);
  assert.deepStrictEqual(splitter.push(': 1}\n'), ['{"a": 1}']);
  assert.deepStrictEqual(splitter.flush(), []);
  splitter.push('last');
  assert.deepStrictEqual(splitter.flush(), ['last']);
});

test('the command lines of a listing, of a file, of one property', () => {
  assert.deepStrictEqual(report.listArguments('f.elpi', ['-I', 'lib']), ['-json', '-list', '-I', 'lib', 'f.elpi']);
  assert.deepStrictEqual(report.checkArguments('f.elpi', undefined, []), ['-json', 'f.elpi']);
  assert.deepStrictEqual(report.checkArguments('f.elpi', 'sort-length', ['-n', '1000']), ['-json', '-p', 'sort-length', '-n', '1000', 'f.elpi']);
  assert.deepStrictEqual(report.includeDirectories(['-n', '10', '-I', 'a', '-I', 'b', '-I']), ['a', 'b']);
});

test('a run of a file: started, passed, failed for each property', () => {
  const follower = new report.RunFollower([property('sort-sorted', 41), property('sort-length', 44), property('rev-agree', 48)]);
  const kinds = [sortSortedProperty, sortSortedResult, sortLengthProperty, sortLengthResult, summary]
    .map(report.parseReportLine)
    .flatMap((event) => follower.handle(event))
    .map((update) => `${update.kind} ${update.property.name}`);
  assert.deepStrictEqual(kinds, ['started sort-sorted', 'passed sort-sorted', 'started sort-length', 'failed sort-length']);
  // rev-agree was expected but not reported: the run ended early
  const end = follower.finish(1, '');
  assert.deepStrictEqual(end.map((update) => `${update.kind} ${update.property.name}`), ['skipped rev-agree']);
});

test('a runtime error: the property being checked is errored, the next ones skipped', () => {
  const follower = new report.RunFollower([property('sort-sorted', 41), property('rev-agree', 48)]);
  follower.handle(report.parseReportLine(sortSortedProperty));
  const updates = follower.handle(report.parseReportLine('{"event":"error","message":"data: Evaluation of a non closed term."}'));
  assert.deepStrictEqual(updates.map((update) => update.kind), ['errored', 'skipped']);
  assert.strictEqual(updates[0].message, 'data: Evaluation of a non closed term.');
  assert.match(updates[1].message, /not checked: the run stopped before it \(data: Evaluation/);
  assert.deepStrictEqual(follower.finish(2, 'data: Evaluation of a non closed term.'), []);
});

test('elpi-check ends without a report (cannot start, killed)', () => {
  const follower = new report.RunFollower([property('rev-agree', 48)]);
  follower.handle(report.parseReportLine(revAgreeProperty));
  const updates = follower.finish(null, '');
  assert.strictEqual(updates[0].kind, 'errored');
  assert.match(updates[0].message, /elpi-check ended \(exit code null\)/);
});

test('the texts of a success and of a failure', () => {
  assert.strictEqual(report.passedText(report.parseReportLine(sortSortedResult)),
                     'passed 100 tests, 0 discarded; average size of the values 11');
  assert.strictEqual(report.failureText(report.parseReportLine(sortLengthResult)), [
    'FAILED at test 23 (22 passed, 0 discarded); counterexample, shrunk in 1 steps:',
    '  L = [0, 0]', '  S = [0]', '  N = 2', '  M = 1',
    'first counterexample:',
    '  L = [-4, 0, 0]', '  S = [-4, 0]', '  N = 3', '  M = 2',
    'replay goal (Debug this counterexample):',
    '  sort [0, 0] S, std.length [0, 0] N, std.length S M, N = M'].join('\n'));
  assert.strictEqual(report.failureText({ status: 'gave-up', passed: 0, discarded: 100 }),
                     'GAVE UP: no test satisfied the premises (100 discarded)');
  assert.strictEqual(report.variablesText(report.parseReportLine(sortSortedProperty).variables),
                     'L : list int (generated), S : list int (computed)');
});

test('the debug configuration of a counterexample: the replay goal on the file', () => {
  const configuration = report.replayConfiguration(report.parseReportLine(sortLengthResult),
                                                   { checkLibrary: '/elpi-tools/check/lib', includeDirectories: ['lib'] });
  assert.deepStrictEqual(configuration, {
    type: 'elpi',
    request: 'launch',
    name: 'Counterexample of sort-length',
    program: lists,
    goal: 'sort [0, 0] S, std.length [0, 0] N, std.length S M, N = M',
    args: ['-I', '/elpi-tools/check/lib', '-I', 'lib'],
    cwd: '/demo',
    stopOnEntry: true
  });
  const withoutLibrary = report.replayConfiguration(report.parseReportLine(sortLengthResult), { checkLibrary: undefined, includeDirectories: [] });
  assert.deepStrictEqual(withoutLibrary.args, []);
});
