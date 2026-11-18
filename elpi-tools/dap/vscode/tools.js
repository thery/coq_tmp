// Where the programs of elpi-tools are, for the modules of the extension
// (debugger.js, properties.js): a setting of the extension, else the build
// of elpi-tools that holds the extension, else the PATH.
'use strict';

const vscode = require('vscode');
const fs = require('fs');
const path = require('path');

// The root of the copy of elpi-tools that holds this extension
// (elpi-tools/dap/vscode -> elpi-tools).
const elpiToolsRoot = path.join(__dirname, '..', '..');

// The bin directory of its build.
const builtBin = path.join(elpiToolsRoot, '_build', 'install', 'default', 'bin');

// [setting(name)]: a setting of the extension (elpiTools.name), '' when
// not set.
function setting(name) {
  return vscode.workspace.getConfiguration('elpiTools').get(name) || '';
}

// [listSetting(name)]: a setting that is a list, [] when not set.
function listSetting(name) {
  const value = vscode.workspace.getConfiguration('elpiTools').get(name);
  return Array.isArray(value) ? value : [];
}

// [programPath(program, settingName)]: the path of one of the programs of
// elpi-tools (elpi-dap, elpi-debug, elpi-check): the setting, else the one
// built next to the extension, else the name alone (found in the PATH).
function programPath(program, settingName) {
  const configured = setting(settingName);
  if (configured) return configured;
  const built = path.join(builtBin, program);
  return fs.existsSync(built) ? built : program;
}

// [checkLibraryPath()]: the directory of property.elpi, which a program
// with properties accumulates (elpi-check finds it by itself, elpi-debug
// needs it with -I): the setting, else elpi-tools/check/lib next to the
// extension, else undefined.
function checkLibraryPath() {
  const configured = setting('checkLibraryPath');
  if (configured) return configured;
  const next = path.join(elpiToolsRoot, 'check', 'lib');
  return fs.existsSync(path.join(next, 'property.elpi')) ? next : undefined;
}

module.exports = { setting, listSetting, programPath, checkLibraryPath };
