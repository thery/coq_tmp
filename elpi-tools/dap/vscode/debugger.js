// The debugger: VS Code starts the debug adapter elpi-dap (DAP on its
// stdin and stdout), which runs elpi-debug -machine on the program.
'use strict';

const vscode = require('vscode');
const fs = require('fs');
const path = require('path');
const tools = require('./tools');

// [adapterPath()]: elpi-dap (see tools.programPath).
function adapterPath() {
  return tools.programPath('elpi-dap', 'adapterPath');
}

// [elpiDebugPath(adapter)]: elpi-debug: the setting, else the one next to
// elpi-dap (undefined: elpi-dap looks for it itself).
function elpiDebugPath(adapter) {
  const configured = tools.setting('elpiDebugPath');
  if (configured) return configured;
  const sibling = path.join(path.dirname(adapter), 'elpi-debug');
  return path.isAbsolute(sibling) && fs.existsSync(sibling) ? sibling : undefined;
}

// Starts elpi-dap for each debugging session.
const adapterFactory = {
  createDebugAdapterDescriptor(_session) {
    return new vscode.DebugAdapterExecutable(adapterPath(), []);
  }
};

// [askGoal(program)]: the goal to debug, typed by the user (undefined if
// the question is dismissed).
function askGoal(program) {
  return vscode.window.showInputBox({ prompt: `The goal to debug in ${path.basename(program)}`, placeHolder: 'main' });
}

// Completes a launch configuration: F5 on an .elpi file without
// launch.json debugs a goal of that file; a configuration with no goal
// asks for it; elpi-debug's path is filled in.
const configurationProvider = {
  async resolveDebugConfiguration(_folder, config) {
    if (!config.type && !config.request && !config.name) {
      const editor = vscode.window.activeTextEditor;
      if (!editor || editor.document.languageId !== 'elpi') return config;
      Object.assign(config, { type: 'elpi', request: 'launch', name: 'Debug an Elpi goal', program: editor.document.fileName, stopOnEntry: true });
    }
    if (!config.elpiDebug) {
      const found = elpiDebugPath(adapterPath());
      if (found) config.elpiDebug = found;
    }
    // the events of the run (Call, Unify, Exit, ...) are written to the
    // Debug Console: open it when the session starts, unless the
    // configuration says otherwise
    if (config.internalConsoleOptions === undefined) {
      config.internalConsoleOptions = 'openOnSessionStart';
    }
    return config;
  },
  // after ${file} and the other variables are replaced: a configuration
  // with no goal asks for it
  async resolveDebugConfigurationWithSubstitutedVariables(_folder, config) {
    if (!config.goal && config.program) {
      const goal = await askGoal(config.program);
      if (!goal) return undefined;
      config.goal = goal;
    }
    return config;
  }
};

function register(context) {
  context.subscriptions.push(vscode.debug.registerDebugAdapterDescriptorFactory('elpi', adapterFactory));
  context.subscriptions.push(vscode.debug.registerDebugConfigurationProvider('elpi', configurationProvider));
}

module.exports = { register };
