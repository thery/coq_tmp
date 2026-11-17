// cyp for VS Code: runs cyp on a Markdown proof, then colours each formula
// by its role, marks each step as proved or not, and puts the goal and
// Rocq's message of a failing step in a diagnostic (shown on hover).

const vscode = require('vscode');
const cp = require('child_process');
const path = require('path');

// The colours: translucent, so that they read in light and dark themes.
function deco(opts) { return vscode.window.createTextEditorDecorationType(opts); }
const styles = {
  var: deco({ backgroundColor: 'rgba(128,128,128,0.20)', borderRadius: '3px' }),
  hyp: deco({ backgroundColor: 'rgba(60,110,230,0.22)', borderRadius: '3px' }),
  fact: deco({ backgroundColor: 'rgba(150,80,200,0.22)', borderRadius: '3px' }),
  claimOk: deco({ backgroundColor: 'rgba(40,170,60,0.25)', borderRadius: '3px' }),
  claimKo: deco({ backgroundColor: 'rgba(220,50,50,0.28)', borderRadius: '3px' }),
  claimNone: deco({ backgroundColor: 'rgba(128,128,128,0.20)', borderRadius: '3px' }),
  markOk: deco({ after: { contentText: '  ✓', color: 'rgb(40,170,60)', fontWeight: 'bold' } }),
  markKo: deco({ after: { contentText: '  ✗', color: 'rgb(220,50,50)', fontWeight: 'bold' } }),
};

const diagnostics = vscode.languages.createDiagnosticCollection('cyp');
const status = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left);
const running = new Set();

// A cyp proof: a Markdown file whose front matter names a preamble or tactics.
function isCypProof(doc) {
  if (doc.languageId !== 'markdown' || doc.lineCount === 0) return false;
  if (doc.lineAt(0).text.trim() !== '---') return false;
  for (let i = 1; i < Math.min(doc.lineCount, 30); i++) {
    const t = doc.lineAt(i).text.trim();
    if (t === '---') return false;
    if (t.startsWith('require:') || t.startsWith('by:')) return true;
  }
  return false;
}

// The ranges of the formulas of a step, in order: each `text` is looked for
// in the lines of the step, after the previous one.
function formulaRanges(doc, step) {
  const out = [];
  let line = step.first, col = 0;
  for (const f of step.formulas) {
    const needle = '`' + f.text + '`';
    for (let l = line; l <= step.last && l < doc.lineCount; l++) {
      const i = doc.lineAt(l).text.indexOf(needle, l === line ? col : 0);
      if (i >= 0) {
        out.push({ role: f.role, range: new vscode.Range(l, i + 1, l, i + 1 + f.text.length) });
        line = l; col = i + needle.length;
        break;
      }
    }
  }
  return out;
}

function show(editor, result) {
  const doc = editor.document;
  const by = {};
  for (const k of Object.keys(styles)) by[k] = [];
  const diags = [];
  let ok = 0, ko = 0;
  for (const step of result.steps) {
    for (const f of formulaRanges(doc, step)) {
      if (f.role === 'claim')
        by[step.status === 'ok' ? 'claimOk' : step.status === 'ko' ? 'claimKo' : 'claimNone'].push(f.range);
      else by[f.role].push(f.range);
    }
    if (step.first >= doc.lineCount) continue;
    const firstLine = doc.lineAt(step.first).range;
    if (step.status === 'ok') { ok++; by.markOk.push(new vscode.Range(firstLine.end, firstLine.end)); }
    if (step.status === 'ko') {
      ko++;
      by.markKo.push(new vscode.Range(firstLine.end, firstLine.end));
      const last = doc.lineAt(Math.min(step.last, doc.lineCount - 1)).range;
      const d = new vscode.Diagnostic(new vscode.Range(firstLine.start, last.end),
        step.message || 'not proved', vscode.DiagnosticSeverity.Error);
      d.source = 'cyp';
      diags.push(d);
    }
  }
  for (const k of Object.keys(styles)) editor.setDecorations(styles[k], by[k]);
  diagnostics.set(doc.uri, diags);
  status.text = ko === 0 ? `$(check) cyp: ${ok} proved` : `$(error) cyp: ${ko} not proved, ${ok} proved`;
  status.show();
}

function check(doc) {
  const key = doc.uri.toString();
  if (running.has(key)) return;
  running.add(key);
  status.text = '$(sync~spin) cyp: checking…';
  status.show();
  const cmd = vscode.workspace.getConfiguration('cyp').get('command');
  const file = doc.uri.fsPath;
  cp.exec(`${cmd} --json "${file.replace(/"/g, '\\"')}"`,
    { cwd: path.dirname(file), maxBuffer: 64 * 1024 * 1024 },
    (err, stdout, stderr) => {
      running.delete(key);
      let result;
      try { result = JSON.parse(stdout); }
      catch (e) {
        status.text = '$(error) cyp: failed';
        vscode.window.showErrorMessage('cyp failed: ' + (stderr || (err && err.message) || stdout).slice(0, 2000));
        return;
      }
      for (const editor of vscode.window.visibleTextEditors)
        if (editor.document.uri.toString() === key) show(editor, result);
    });
}

function activate(context) {
  context.subscriptions.push(
    diagnostics, status,
    vscode.commands.registerCommand('cyp.check', () => {
      const e = vscode.window.activeTextEditor;
      if (e) check(e.document);
    }),
    vscode.workspace.onDidSaveTextDocument(doc => {
      if (vscode.workspace.getConfiguration('cyp').get('checkOnSave') && isCypProof(doc)) check(doc);
    }),
    vscode.window.onDidChangeActiveTextEditor(e => {
      if (e && isCypProof(e.document) && vscode.workspace.getConfiguration('cyp').get('checkOnSave')) check(e.document);
    }));
  const e = vscode.window.activeTextEditor;
  if (e && isCypProof(e.document)) check(e.document);
}

function deactivate() {}

module.exports = { activate, deactivate };
