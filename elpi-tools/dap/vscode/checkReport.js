// The report of elpi-check -json, read for the Test Explorer: one JSON
// object per line (elpi-tools/check/lib/machine.elpi, check/README.md),
// events "property", "result", "summary", "error".  This module does not
// use VS Code, so that it is tested in Node (test/checkReport.test.js);
// properties.js shows what it computes.
'use strict';

const path = require('path');

// -- The command lines -----------------------------------------------------

// [listArguments(file, extraArgs)]: the arguments of elpi-check that list
// the properties of a file, without testing them.
function listArguments(file, extraArgs) {
  return ['-json', '-list', ...extraArgs, file];
}

// [checkArguments(file, propertyName, extraArgs)]: the arguments of
// elpi-check that test the properties of a file, or only the one named
// (propertyName undefined: all of them).
function checkArguments(file, propertyName, extraArgs) {
  const only = propertyName === undefined ? [] : ['-p', propertyName];
  return ['-json', ...only, ...extraArgs, file];
}

// [includeDirectories(args)]: the directories DIR of the options -I DIR
// among the arguments of elpi-check (the debugger needs them too).
function includeDirectories(args) {
  const directories = [];
  for (let i = 0; i + 1 < args.length; i++) {
    if (args[i] === '-I') directories.push(args[i + 1]);
  }
  return directories;
}

// -- Reading the output ----------------------------------------------------

// [parseReportLine(line)]: the event of one line of the report, or null
// for a line that is not one (a print of the program under test).
function parseReportLine(line) {
  const text = line.trim();
  if (!text.startsWith('{')) return null;
  let event;
  try {
    event = JSON.parse(text);
  } catch (_error) {
    return null;
  }
  return typeof event === 'object' && event !== null && typeof event.event === 'string' ? event : null;
}

// Splits the output of elpi-check, received in chunks, into lines.
class LineSplitter {
  constructor() {
    this.pending = '';
  }

  // [push(chunk)]: the complete lines that the chunk ends.
  push(chunk) {
    const lines = (this.pending + chunk).split('\n');
    this.pending = lines.pop();
    return lines;
  }

  // [flush()]: the last line, when the output does not end with a newline.
  flush() {
    const last = this.pending;
    this.pending = '';
    return last === '' ? [] : [last];
  }
}

// [propertyOfEvent(event)]: the property that an event "property" or
// "result" is about.
function propertyOfEvent(event) {
  return { name: event.name, file: event.file, line: event.line, variables: event.variables || [] };
}

// -- The outcome of a run ----------------------------------------------------

// Follows a run of elpi-check -json on a file, event by event, and says
// what happens to each property: an update is
//   { kind: 'started', property }
//   { kind: 'passed', property, result }
//   { kind: 'failed', property, result }     (status failed or gave-up)
//   { kind: 'errored', property, message }   (the run stopped on it)
//   { kind: 'skipped', property, message }   (expected, never reached)
// The expected properties are those that the run should check (all those
// of the file, or the one asked with -p), as listed before.
class RunFollower {
  constructor(expectedProperties) {
    this.waiting = new Map(expectedProperties.map((property) => [property.name, property]));
    this.current = undefined;
  }

  // [handle(event)]: the updates for one event.
  handle(event) {
    switch (event.event) {
      case 'property':
        this.current = propertyOfEvent(event);
        return [{ kind: 'started', property: this.current }];
      case 'result': {
        const property = propertyOfEvent(event);
        this.waiting.delete(property.name);
        this.current = undefined;
        const kind = event.status === 'ok' ? 'passed' : 'failed';
        return [{ kind, property, result: event }];
      }
      case 'error':
        return this.stop(event.message);
      default:
        return [];
    }
  }

  // [finish(exitCode, errorText)]: the updates when elpi-check has ended:
  // the properties not reported are errored (the one being checked) or
  // skipped (the others), with the error text of the run.
  finish(exitCode, errorText) {
    if (this.waiting.size === 0 && this.current === undefined) return [];
    const message = errorText || `elpi-check ended (exit code ${exitCode}) before reporting this property`;
    return this.stop(message);
  }

  // [stop(message)]: the run stopped: the property being checked is
  // errored, the ones not reached are skipped.
  stop(message) {
    const updates = [];
    if (this.current !== undefined) {
      updates.push({ kind: 'errored', property: this.current, message });
      this.waiting.delete(this.current.name);
      this.current = undefined;
    }
    for (const property of this.waiting.values()) {
      updates.push({ kind: 'skipped', property, message: `not checked: the run stopped before it (${firstLine(message)})` });
    }
    this.waiting.clear();
    return updates;
  }
}

function firstLine(text) {
  return String(text).split('\n')[0];
}

// -- What is shown ---------------------------------------------------------

// [bindingsText(bindings, indent)]: the lines "X = value" of a
// counterexample.
function bindingsText(bindings, indent) {
  return bindings.map((binding) => `${indent}${binding.name} = ${binding.value}`).join('\n');
}

// [passedText(result)]: the line shown for a property that holds.
function passedText(result) {
  return `passed ${result.passed} tests, ${result.discarded} discarded; average size of the values ${result['average-size']}`;
}

// [failureText(result)]: the message of a failed property: the shrunk
// counterexample, the counts, the first counterexample.
function failureText(result) {
  if (result.status === 'gave-up') {
    return `GAVE UP: no test satisfied the premises (${result.discarded} discarded)`;
  }
  return [
    `FAILED at test ${result['failed-at-test']} (${result.passed} passed, ${result.discarded} discarded); counterexample, shrunk in ${result['shrink-steps']} steps:`,
    bindingsText(result.shrunk, '  '),
    'first counterexample:',
    bindingsText(result.first, '  '),
    'replay goal (Debug this counterexample):',
    `  ${result.replay}`
  ].join('\n');
}

// [variablesText(variables)]: "L : list int (generated), .."
function variablesText(variables) {
  return variables.map((v) => `${v.name} : ${v.type} (${v.kind})`).join(', ');
}

// -- Debugging a counterexample --------------------------------------------

// [replayConfiguration(result, options)]: the launch configuration of the
// debugger (type elpi) that runs the replay goal of a failed property on
// its file: options.checkLibrary is the directory of property.elpi (or
// undefined), options.includeDirectories the -I of elpi-check.  It stops
// on entry, before the first event, so that one steps into the goal.
function replayConfiguration(result, options) {
  const directories = [];
  if (options.checkLibrary) directories.push(options.checkLibrary);
  directories.push(...options.includeDirectories);
  const args = [];
  for (const directory of directories) args.push('-I', directory);
  return {
    type: 'elpi',
    request: 'launch',
    name: `Counterexample of ${result.name}`,
    program: result.file,
    goal: result.replay,
    args,
    cwd: path.dirname(result.file),
    stopOnEntry: true,
    // the first stop, before the first call, is shown on the property
    queryPath: result.file,
    queryLine: result.line
  };
}

// [debugHeaderText(result)]: what the Debug Console says when the debugger
// starts on a counterexample: the property, the values, the goal, what to do.
function debugHeaderText(result) {
  const lines = [`Debugging the counterexample of the property ${result.name} (${path.basename(result.file)}:${result.line}):`];
  lines.push(bindingsText(result.shrunk, '  '));
  lines.push(`The goal: ${result.replay}`);
  lines.push('Stopped before the first call: Step Into (F11) to follow the run, Continue (F5) to its end.');
  return lines.join('\n') + '\n';
}

module.exports = {
  debugHeaderText,
  listArguments,
  checkArguments,
  includeDirectories,
  parseReportLine,
  LineSplitter,
  propertyOfEvent,
  RunFollower,
  passedText,
  failureText,
  variablesText,
  replayConfiguration
};
