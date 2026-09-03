// Strict, fail-closed kernel audit. Run after the serial import-closure build.
import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const audits = ['ShortRingAnchor/Audit.lean', 'ShortRingAnchor/HighBandIntegrationAudit.lean'];
const allowed = new Set(['propext', 'Classical.choice', 'Quot.sound']);
function checkReports(output, expected) {
  const reports = new Map();
  for (const m of output.matchAll(/'([^'\r\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)/g)) {
    const name = m[1], axioms = (m[2] ?? '').split(',').map(x => x.trim()).filter(Boolean);
    if (reports.has(name)) throw new Error(`Duplicate axiom report: ${name}`);
    if (!expected.includes(name)) throw new Error(`Unexpected axiom report: ${name}`);
    for (const axiom of axioms) if (!allowed.has(axiom)) throw new Error(`Unapproved axiom: ${name}: ${axiom}`);
    reports.set(name, axioms);
  }
  if (/\bsorryAx\b|\berror:|declaration uses 'sorry'/.test(output)) throw new Error('Lean error or placeholder in audit output.');
  for (const name of expected) if (!reports.has(name)) throw new Error(`Missing axiom report: ${name}`);
  return Object.fromEntries(reports);
}
function selfTest() {
  assert.deepEqual(checkReports("'A' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n'B' does not depend on any axioms", ['A', 'B']),
    { A: ['propext', 'Classical.choice', 'Quot.sound'], B: [] });
  for (const bad of ['', "'A' depends on axioms: [sorryAx]", "'A' depends on axioms: [MyAxiom]",
    "'A' depends on axioms: []\n'A' depends on axioms: []", "'B' depends on axioms: []",
    "'A' depends on axioms: []\nerror: failed"]) assert.throws(() => checkReports(bad, ['A']));
  console.log('Axiom-audit parser self-tests passed.');
}
selfTest();
if (process.argv.includes('--self-test')) process.exit(0);
const outDir = path.join(root, 'audit', 'verification');
fs.mkdirSync(outDir, { recursive: true });
async function run(command, args, logName) {
  const log = fs.createWriteStream(path.join(outDir, logName));
  let output = '';
  console.log(`RUN ${command} ${args.join(' ')}`);
  const child = spawn(command, args, { cwd: root, stdio: ['ignore', 'pipe', 'pipe'] });
  for (const stream of [child.stdout, child.stderr]) stream.on('data', chunk => {
    log.write(chunk); output += chunk;
  });
  const code = await new Promise((resolve, reject) => {
    child.on('error', reject); child.on('close', resolve);
  });
  await new Promise(resolve => log.end(resolve));
  if (code !== 0) {
    console.error(output.slice(-16000));
    throw new Error(`${command} failed with status ${code}; see ${logName}`);
  }
  return output;
}
const hygiene = JSON.parse(await run(process.execPath, ['scripts/audit-lean-sources.mjs'], 'source-hygiene.json'));
await run('lake', ['--no-cache', 'build'], 'lake-build.log');
const results = {};
for (const file of audits) {
  const expected = [...fs.readFileSync(path.join(root, file), 'utf8').matchAll(/^#print axioms (\S+)\s*$/gm)].map(m => m[1]);
  if (!expected.length || new Set(expected).size !== expected.length) throw new Error(`Invalid audit declaration list: ${file}`);
  const output = await run('lake', ['env', 'lean', '-j', '1', file], path.basename(file, '.lean') + '.log');
  results[file] = checkReports(output, expected);
  console.log(`PASS ${file}: ${expected.length} exact axiom reports.`);
}
const summary = {
  status: 'passed', commit: process.env.GITHUB_SHA ?? null, timeUTC: new Date().toISOString(),
  leanSourceFiles: hygiene.files, normalLakeBuild: 'passed',
  reportCount: Object.values(results).reduce((n, r) => n + Object.keys(r).length, 0),
  uniqueDeclarations: new Set(Object.values(results).flatMap(r => Object.keys(r))).size,
  allowedAxioms: [...allowed], audits: results,
  scope: 'Kernel verification of the stated conditional theorems; explicit mathematical hypotheses are not discharged by an axiom audit.'
};
fs.writeFileSync(path.join(outDir, 'summary.json'), JSON.stringify(summary, null, 2) + '\n');
console.log(`PASS: normal lake build; ${summary.reportCount} reports, ${summary.uniqueDeclarations} distinct declarations; ${hygiene.files} source files.`);
