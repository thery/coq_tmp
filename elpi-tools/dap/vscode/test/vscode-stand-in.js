// A stand-in for the module vscode, for the tests in Node: the parts of the
// API that the extension uses, recording what the extension does with
// them (the test runs, the debugging sessions started, the commands).
// Not VS Code: what VS Code draws from these calls is not tested.
'use strict';

const path = require('path');

// What the extension did, for the tests to look at.
const recorded = {
  runs: [],              // the test runs created (StandInTestRun)
  debugSessions: [],     // the configurations given to debug.startDebugging
  commands: new Map(),   // command name -> handler
  informationMessages: []
};

// The settings of the extension (elpiTools.*), set by the tests.
const settings = {};

class Uri {
  constructor(fsPath) {
    this.scheme = 'file';
    this.fsPath = fsPath;
    this.path = fsPath;
  }
  static file(fsPath) {
    return new Uri(fsPath);
  }
  toString() {
    return `file://${this.fsPath}`;
  }
}

class Position {
  constructor(line, character) {
    this.line = line;
    this.character = character;
  }
}

class Range {
  constructor(startLine, startCharacter, endLine, endCharacter) {
    this.start = new Position(startLine, startCharacter);
    this.end = new Position(endLine, endCharacter);
  }
}

class Location {
  constructor(uri, range) {
    this.uri = uri;
    this.range = range;
  }
}

class TestMessage {
  constructor(message) {
    this.message = message;
  }
}

// The children of an item, or the root items of a controller.
class TestItemCollection {
  constructor(parent) {
    this.parent = parent;
    this.items = new Map();
  }
  get size() {
    return this.items.size;
  }
  get(id) {
    return this.items.get(id);
  }
  add(item) {
    item.parent = this.parent;
    this.items.set(item.id, item);
  }
  delete(id) {
    this.items.delete(id);
  }
  replace(items) {
    this.items.clear();
    items.forEach((item) => this.add(item));
  }
  forEach(callback) {
    this.items.forEach((item) => callback(item, this));
  }
}

class TestItem {
  constructor(id, label, uri) {
    this.id = id;
    this.label = label;
    this.uri = uri;
    this.parent = undefined;
    this.children = new TestItemCollection(this);
    this.range = undefined;
    this.description = undefined;
    this.error = undefined;
  }
}

// A test run: the states given to each item, in order.
class StandInTestRun {
  constructor(request) {
    this.request = request;
    this.states = [];      // { state, id, message }
    this.output = '';
    this.ended = false;
  }
  record(state, item, message) {
    this.states.push({ state, id: item.id, message });
  }
  enqueued(item) { this.record('enqueued', item); }
  started(item) { this.record('started', item); }
  passed(item) { this.record('passed', item); }
  failed(item, message) { this.record('failed', item, message); }
  errored(item, message) { this.record('errored', item, message); }
  skipped(item) { this.record('skipped', item); }
  appendOutput(text) { this.output += text; }
  end() { this.ended = true; }
  // [finalState(id)]: the last state given to an item
  finalState(id) {
    const states = this.states.filter((s) => s.id === id && s.state !== 'enqueued' && s.state !== 'started');
    return states.length === 0 ? undefined : states[states.length - 1];
  }
}

class TestController {
  constructor(id, label) {
    this.id = id;
    this.label = label;
    this.items = new TestItemCollection(undefined);
    this.profiles = [];
    this.resolveHandler = undefined;
    this.refreshHandler = undefined;
  }
  createTestItem(id, label, uri) {
    return new TestItem(id, label, uri);
  }
  createRunProfile(label, kind, runHandler, isDefault) {
    const profile = { label, kind, runHandler, isDefault };
    this.profiles.push(profile);
    return profile;
  }
  createTestRun(request) {
    const run = new StandInTestRun(request);
    recorded.runs.push(run);
    return run;
  }
  dispose() {}
}

const controllers = [];

// A cancellation token that is never cancelled.
const neverCancelled = { isCancellationRequested: false, onCancellationRequested: () => ({ dispose() {} }) };

const disposable = { dispose() {} };

module.exports = {
  // the parts of the API
  Uri,
  Position,
  Range,
  Location,
  TestMessage,
  TestRunProfileKind: { Run: 1, Debug: 2, Coverage: 3 },
  DebugAdapterExecutable: class { constructor(command, args) { this.command = command; this.args = args; } },
  tests: {
    createTestController(id, label) {
      const controller = new TestController(id, label);
      controllers.push(controller);
      return controller;
    }
  },
  workspace: {
    textDocuments: [],
    getConfiguration(_section) {
      return { get: (name) => settings[name] };
    },
    getWorkspaceFolder(_uri) { return undefined; },
    onDidOpenTextDocument() { return disposable; },
    onDidSaveTextDocument() { return disposable; }
  },
  window: {
    activeTextEditor: undefined,
    createOutputChannel(_name) {
      return { lines: [], appendLine(text) { this.lines.push(text); }, dispose() {} };
    },
    showInformationMessage(text) { recorded.informationMessages.push(text); return Promise.resolve(undefined); },
    showInputBox() { return Promise.resolve(undefined); }
  },
  debug: {
    registerDebugAdapterDescriptorFactory() { return disposable; },
    registerDebugConfigurationProvider() { return disposable; },
    startDebugging(_folder, configuration) {
      recorded.debugSessions.push(configuration);
      return Promise.resolve(true);
    }
  },
  commands: {
    registerCommand(name, handler) {
      recorded.commands.set(name, handler);
      return disposable;
    }
  },
  // for the tests
  standIn: { recorded, settings, controllers, neverCancelled, documentOf: (file) => ({ uri: Uri.file(file), fileName: file, languageId: path.extname(file) === '.elpi' ? 'elpi' : 'plaintext' }) }
};
