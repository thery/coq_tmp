// The properties of elpi-check in VS Code's Testing API.
//
// - Discovery: for each .elpi file opened (and again when it is saved),
//   `elpi-check -json -list FILE` lists its properties; the Test Explorer
//   shows the file with its properties, and each property gets the run
//   buttons in the margin of its line.
// - Run: one property (`-p NAME`), a file, or all, through
//   `elpi-check -json`; the result is shown on the property's line, a
//   failure with its shrunk counterexample and the counts.
// - "Debug this counterexample": the debugger (debug type elpi, see
//   debugger.js) runs the replay goal of the failure (check/README.md,
//   "Replaying a counterexample"), stopped before its first event.  From
//   the failure message, from the context menu of a property, or with the
//   Debug profile (runs the property, then debugs its failure).
//
// The reading of the report is in checkReport.js (no VS Code there).
'use strict';

const vscode = require('vscode');
const childProcess = require('child_process');
const path = require('path');
const tools = require('./tools');
const report = require('./checkReport');

const controllerId = 'elpiProperties';
const debugCommand = 'elpiTools.debugCounterexample';

// The context value of a failure message: the menu testing/message/content
// of package.json shows "Debug this counterexample" on it.
const counterexampleContext = 'elpiCounterexample';

// [elpiCheckPath()]: elpi-check (see tools.programPath).
function elpiCheckPath() {
  return tools.programPath('elpi-check', 'checkPath');
}

// [extraArguments()]: more options of elpi-check (setting checkArgs).
function extraArguments() {
  return tools.listSetting('checkArgs');
}

// [isElpiFile(document)]: a document saved as an .elpi file.
function isElpiFile(document) {
  return document.uri.scheme === 'file' && document.fileName.endsWith('.elpi');
}

// [propertyId(file, name)]: the id of the test item of a property.
function propertyId(file, name) {
  return `${file}#${name}`;
}

// [runElpiCheck(args, cwd, onEvent, token)]: runs elpi-check in cwd,
// calls onEvent on each event of its report as it comes; resolves to
// { exitCode, errorText } (errorText: what it printed on stderr).  A
// cancellation kills it.
function runElpiCheck(args, cwd, onEvent, token) {
  return new Promise((resolve) => {
    const child = childProcess.spawn(elpiCheckPath(), args, { cwd });
    const lines = new report.LineSplitter();
    let errorText = '';
    const deliver = (line) => {
      const event = report.parseReportLine(line);
      if (event) onEvent(event);
    };
    const cancellation = token ? token.onCancellationRequested(() => child.kill()) : undefined;
    child.stdout.setEncoding('utf8');
    child.stderr.setEncoding('utf8');
    child.stdout.on('data', (chunk) => lines.push(chunk).forEach(deliver));
    child.stderr.on('data', (chunk) => { errorText += chunk; });
    child.on('error', (error) => { errorText += `cannot run ${elpiCheckPath()}: ${error.message}`; });
    child.on('close', (exitCode) => {
      lines.flush().forEach(deliver);
      if (cancellation) cancellation.dispose();
      resolve({ exitCode, errorText: errorText.trim() });
    });
  });
}

// The test items of the properties, their runs and their failures.
class PropertyTests {
  constructor(controller, output) {
    this.controller = controller;
    this.output = output;
    // the property (name, file, line, variables) of each property item
    this.properties = new WeakMap();
    // the last failure of each property (its result event), by item id
    this.failures = new Map();
  }

  // [propertyOf(item)]: the property of an item, undefined for a file item.
  propertyOf(item) {
    return this.properties.get(item);
  }

  // -- Discovery -------------------------------------------------------------

  // [discover(file)]: lists the properties of the file and updates its
  // item: one child per property, on its line.  A file without
  // properties has no item; a file that does not compile keeps its items,
  // with the error.
  async discover(file) {
    const events = [];
    const run = await runElpiCheck(report.listArguments(file, extraArguments()), path.dirname(file),
                                   (event) => events.push(event));
    const properties = events.filter((event) => event.event === 'property').map(report.propertyOfEvent);
    const errorEvent = events.find((event) => event.event === 'error');
    if (errorEvent || run.exitCode === 2) {
      this.log(`elpi-check -list ${file}: ${errorEvent ? errorEvent.message : run.errorText}`);
      const existing = this.controller.items.get(file);
      if (existing) existing.error = errorEvent ? errorEvent.message : run.errorText;
      return;
    }
    if (properties.length === 0) {
      this.controller.items.delete(file);
      return;
    }
    const fileItem = this.fileItem(file);
    fileItem.error = undefined;
    fileItem.children.replace(properties.map((property) => this.propertyItem(property)));
  }

  // [fileItem(file)]: the item of a file, created if needed.
  fileItem(file) {
    let item = this.controller.items.get(file);
    if (!item) {
      item = this.controller.createTestItem(file, path.basename(file), vscode.Uri.file(file));
      this.controller.items.add(item);
    }
    return item;
  }

  // [propertyItem(property)]: a new item for a property, at its line (in
  // its own file, which may be accumulated by the file checked).
  propertyItem(property) {
    const item = this.controller.createTestItem(propertyId(property.file, property.name), property.name,
                                                vscode.Uri.file(property.file));
    const line = Math.max(property.line - 1, 0);
    item.range = new vscode.Range(line, 0, line, 0);
    item.description = report.variablesText(property.variables);
    this.properties.set(item, property);
    return item;
  }

  // -- Runs ------------------------------------------------------------------

  // [runRequest(request, token, debugFailures)]: runs the items asked
  // (all when none); with debugFailures, then debugs the first failure.
  async runRequest(request, token, debugFailures) {
    const run = this.controller.createTestRun(request);
    const firstFailures = [];
    try {
      for (const job of this.jobs(request)) {
        if (token.isCancellationRequested) break;
        job.items.forEach((item) => run.enqueued(item));
        const failure = await this.runJob(job, run, token);
        if (failure) firstFailures.push(failure);
      }
    } finally {
      run.end();
    }
    if (!debugFailures) return;
    if (firstFailures.length > 0) await this.debugFailure(firstFailures[0]);
    else vscode.window.showInformationMessage('No counterexample to debug: the properties run hold.');
  }

  // [jobs(request)]: the runs of elpi-check that a request needs: per file,
  // the whole file when the file (or the whole tree) is asked, else one
  // run per property (-p).  A job is { file, propertyName, items }.
  jobs(request) {
    const excluded = new Set((request.exclude || []).map((item) => item.id));
    const asked = request.include ? request.include : this.allItems(this.controller.items);
    const jobs = [];
    for (const item of asked) {
      if (excluded.has(item.id)) continue;
      if (this.propertyOf(item)) {
        jobs.push({ file: this.checkedFile(item), propertyName: this.propertyOf(item).name, items: [item] });
      } else {
        const children = this.allItems(item.children).filter((child) => !excluded.has(child.id));
        const all = children.length === item.children.size;
        if (all) jobs.push({ file: item.id, propertyName: undefined, items: children });
        else children.forEach((child) => jobs.push({ file: item.id, propertyName: this.propertyOf(child).name, items: [child] }));
      }
    }
    return jobs;
  }

  // [checkedFile(item)]: the file given to elpi-check for a property
  // item: the file of its parent item.
  checkedFile(item) {
    return item.parent ? item.parent.id : this.propertyOf(item).file;
  }

  // [allItems(collection)]: the items of a collection, as an array.
  allItems(collection) {
    const items = [];
    collection.forEach((item) => items.push(item));
    return items;
  }

  // [runJob(job, run, token)]: one run of elpi-check, its events shown on
  // the items; resolves to the first failure (a result event), if any.
  async runJob(job, run, token) {
    const itemsByName = new Map(job.items.map((item) => [this.propertyOf(item).name, item]));
    const follower = new report.RunFollower(job.items.map((item) => this.propertyOf(item)));
    let firstFailure;
    const show = (update) => {
      const item = itemsByName.get(update.property.name);
      if (!item) return;
      const failure = this.showUpdate(run, item, update);
      if (failure && !firstFailure) firstFailure = failure;
    };
    const args = report.checkArguments(job.file, job.propertyName, extraArguments());
    this.log(`elpi-check ${args.join(' ')}`);
    const outcome = await runElpiCheck(args, path.dirname(job.file),
                                       (event) => follower.handle(event).forEach(show), token);
    if (outcome.errorText) this.log(outcome.errorText);
    follower.finish(outcome.exitCode, outcome.errorText).forEach(show);
    return firstFailure;
  }

  // [showUpdate(run, item, update)]: shows an update of the follower on
  // the item; returns the result of a failure.
  showUpdate(run, item, update) {
    switch (update.kind) {
      case 'started':
        run.started(item);
        return undefined;
      case 'passed':
        this.failures.delete(item.id);
        run.appendOutput(`${item.label}: ${report.passedText(update.result)}\r\n`, undefined, item);
        run.passed(item);
        return undefined;
      case 'failed': {
        const message = new vscode.TestMessage(report.failureText(update.result));
        message.location = new vscode.Location(item.uri, item.range);
        if (update.result.replay) {
          message.contextValue = counterexampleContext;
          this.failures.set(item.id, update.result);
        }
        run.failed(item, message);
        return update.result.replay ? update.result : undefined;
      }
      case 'errored': {
        const message = new vscode.TestMessage(update.message);
        message.location = new vscode.Location(item.uri, item.range);
        run.errored(item, message);
        return undefined;
      }
      case 'skipped':
        run.appendOutput(`${item.label}: ${update.message}\r\n`, undefined, item);
        run.skipped(item);
        return undefined;
      default:
        return undefined;
    }
  }

  // -- Debugging a counterexample --------------------------------------------

  // [debugFailure(result)]: starts the debugger on the replay goal of a
  // failed property.
  async debugFailure(result) {
    const configuration = report.replayConfiguration(result, {
      checkLibrary: tools.checkLibraryPath(),
      includeDirectories: report.includeDirectories(extraArguments())
    });
    this.log(`debug ${configuration.program}: ${configuration.goal}`);
    const folder = vscode.workspace.getWorkspaceFolder(vscode.Uri.file(result.file));
    const started = await vscode.debug.startDebugging(folder, configuration);
    if (started) vscode.debug.activeDebugConsole.append(report.debugHeaderText(result));
    else vscode.window.showErrorMessage(`The debugger did not start on the counterexample of ${result.name}.`);
    return started;
  }

  // [debugCommand(argument)]: the command "Debug this counterexample", from
  // a failure message ({ test, message }) or a property item.
  async debugCommand(argument) {
    const item = argument && argument.test ? argument.test : argument;
    const result = item ? this.failures.get(item.id) : undefined;
    if (!result) {
      vscode.window.showInformationMessage('No counterexample for this property: run it first (it must fail).');
      return undefined;
    }
    return this.debugFailure(result);
  }

  // [log(text)]: a line in the output channel "Elpi properties".
  log(text) {
    this.output.appendLine(text);
  }
}

// [register(context)]: the test controller, its profiles, the discovery
// on the open and saved .elpi files, the command.
function register(context) {
  const controller = vscode.tests.createTestController(controllerId, 'Elpi properties');
  const output = vscode.window.createOutputChannel('Elpi properties');
  const tests = new PropertyTests(controller, output);
  context.subscriptions.push(controller, output);

  const discoverDocument = (document) => {
    if (isElpiFile(document)) tests.discover(document.fileName);
  };
  const discoverOpenDocuments = () => Promise.all(vscode.workspace.textDocuments.filter(isElpiFile)
                                                  .map((document) => tests.discover(document.fileName)));

  controller.resolveHandler = async (item) => {
    if (!item) await discoverOpenDocuments();
  };
  controller.refreshHandler = async () => {
    const known = tests.allItems(controller.items).map((item) => item.id);
    await Promise.all(known.map((file) => tests.discover(file)));
    await discoverOpenDocuments();
  };
  controller.createRunProfile('Check', vscode.TestRunProfileKind.Run,
                              (request, token) => tests.runRequest(request, token, false), true);
  controller.createRunProfile('Debug counterexample', vscode.TestRunProfileKind.Debug,
                              (request, token) => tests.runRequest(request, token, true), true);

  context.subscriptions.push(
    vscode.workspace.onDidOpenTextDocument(discoverDocument),
    vscode.workspace.onDidSaveTextDocument(discoverDocument),
    vscode.commands.registerCommand(debugCommand, (argument) => tests.debugCommand(argument)));
  discoverOpenDocuments();
  return tests;
}

module.exports = { register, PropertyTests, propertyId };
