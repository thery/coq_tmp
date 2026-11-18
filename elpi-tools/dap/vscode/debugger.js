// The debugger: VS Code starts the debug adapter elpi-dap (DAP on its
// stdin and stdout), which runs elpi-debug -machine on the program.
'use strict';

const vscode = require('vscode');
const fs = require('fs');
const path = require('path');

// The bin directory of a build of elpi-tools that holds this extension
// (elpi-tools/dap/vscode -> elpi-tools/_build/install/default/bin).
const builtBin = path.join(__dirname, '..', '..', '_build', 'install', 'default', 'bin');

// [setting(name)]: a setting of the extension, '' when not set.
function setting(name) {
  return vscode.workspace.getConfiguration('elpiTools').get(name) || '';
}

// [adapterPath()]: elpi-dap: the setting, else the one built next to the
// extension, else the one of the PATH.
function adapterPath() {
  const configured = setting('adapterPath');
  if (configured) return configured;
  const built = path.join(builtBin, 'elpi-dap');
  return fs.existsSync(built) ? built : 'elpi-dap';
}

// [elpiDebugPath(adapter)]: elpi-debug: the setting, else the one next to
// elpi-dap (undefined: elpi-dap looks for it itself).
function elpiDebugPath(adapter) {
  const configured = setting('elpiDebugPath');
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
