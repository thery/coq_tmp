// The extension "Elpi tools": one entry point, one module per tool.
// Today the debugger (debugger.js); the properties of elpi-check
// (tests, "debug this counterexample") are meant to be another module
// registered here.
'use strict';

const debuggerPart = require('./debugger');

function activate(context) {
  debuggerPart.register(context);
}

function deactivate() {}

module.exports = { activate, deactivate };
