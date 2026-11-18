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

// Completes a launch configuration: F5 on an .elpi file without
// launch.json asks for a goal; elpi-debug's path is filled in.
const configurationProvider = {
  async resolveDebugConfiguration(_folder, config) {
    if (!config.type && !config.request && !config.name) {
      const editor = vscode.window.activeTextEditor;
      if (!editor || editor.document.languageId !== 'elpi') return config;
      const goal = await vscode.window.showInputBox({ prompt: 'The goal to debug', placeHolder: 'main' });
      if (!goal) return undefined;
      Object.assign(config, { type: 'elpi', request: 'launch', name: 'Debug an Elpi goal', program: editor.document.fileName, goal: goal, stopOnEntry: true });
    }
    if (!config.elpiDebug) {
      const found = elpiDebugPath(adapterPath());
      if (found) config.elpiDebug = found;
    }
    return config;
  }
};

function register(context) {
  context.subscriptions.push(vscode.debug.registerDebugAdapterDescriptorFactory('elpi', adapterFactory));
  context.subscriptions.push(vscode.debug.registerDebugConfigurationProvider('elpi', configurationProvider));
}

module.exports = { register };
