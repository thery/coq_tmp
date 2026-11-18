// The extension "Elpi tools": one entry point, one module per tool.
// - debugger.js: the debugger (elpi-debug, through the adapter elpi-dap);
// - properties.js: the properties of elpi-check as tests of the Test
//   Explorer, with "Debug this counterexample" (which uses the debugger).
// tools.js finds the programs of elpi-tools; checkReport.js reads the
// report of elpi-check (no VS Code there, tested in Node).
'use strict';

const debuggerPart = require('./debugger');
const propertiesPart = require('./properties');

function activate(context) {
  debuggerPart.register(context);
  propertiesPart.register(context);
}

function deactivate() {}

module.exports = { activate, deactivate };
