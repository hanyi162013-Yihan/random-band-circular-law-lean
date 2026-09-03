// Source hygiene only. This does not replace kernel checking or #print axioms.
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
function collect(dir) {
  return fs.readdirSync(dir, { withFileTypes: true }).flatMap(entry => {
    if (entry.name.startsWith('.')) return [];
    const file = path.join(dir, entry.name);
    return entry.isDirectory() ? collect(file) : file.endsWith('.lean') ? [file] : [];
  });
}
function codeOnly(text) {
  let out = '', depth = 0, string = false, lineComment = false;
  for (let i = 0; i < text.length; ++i) {
    const c = text[i], pair = text.slice(i, i + 2);
    if (c === '\n') {
      out += '\n'; lineComment = false; continue;
    }
    if (lineComment) { out += ' '; continue; }
    if (depth) {
      if (pair === '/-') { ++depth; ++i; out += '  '; }
      else if (pair === '-/') { --depth; ++i; out += '  '; }
      else out += ' ';
      continue;
    }
    if (string) {
      if (c === '\\') { ++i; out += '  '; }
      else { if (c === '"') string = false; out += ' '; }
      continue;
    }
    if (pair === '--') { lineComment = true; ++i; out += '  '; }
    else if (pair === '/-') { depth = 1; ++i; out += '  '; }
    else if (c === '"') { string = true; out += ' '; }
    else out += c;
  }
  if (depth || string) throw new Error('Unclosed comment or string in source scan.');
  return out;
}
const files = collect(root), violations = [], options = new Set();
for (const file of files) {
  const code = codeOnly(fs.readFileSync(file, 'utf8'));
  for (const match of code.matchAll(/\b(?:sorry|sorryAx|admit|unsafe|axiom|native_decide)\b/g)) {
    violations.push({ file: path.relative(root, file),
      line: code.slice(0, match.index).split('\n').length, token: match[0] });
  }
  for (const match of code.matchAll(/\bset_option\s+([\w.]+)\s+([^\s]+)/g)) {
    options.add(`${match[1]} ${match[2]}`);
    if (!/^(?:maxHeartbeats|maxRecDepth|autoImplicit)$|^linter\./.test(match[1])) {
      violations.push({ file: path.relative(root, file), option: match[0] });
    }
  }
}
console.log(JSON.stringify({ files: files.length, violations,
  options: [...options].sort(), excludes: ['.lake and other hidden directories', 'comments', 'strings'],
  note: 'Source scan only; use successful lake builds and kernel axiom audits as certificates.' }, null, 2));
if (violations.length) process.exitCode = 1;
