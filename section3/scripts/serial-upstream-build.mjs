// Build the copied dependency closure serially, using only local sources.
// No cache downloads, package updates, deletion, or other-project mutation.
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const requested = process.argv.slice(2);
if (!requested.length) throw new Error('Supply the Lean module targets to check.');
const seen = new Set();
const pending = [];
function visit(module) {
  if (seen.has(module)) return;
  seen.add(module);
  if (module === 'Mathlib') throw new Error('Refusing an umbrella Mathlib build.');
  let base;
  if (module === 'ShortRingAnchor' || module.startsWith('Vendor.') || module.startsWith('ShortRingAnchor.')) base = root;
  else if (module.startsWith('Mathlib.')) base = path.join(root, '.lake/packages/mathlib');
  else return; // The already installed auxiliary packages are managed by Lake.
  const rel = module.replaceAll('.', '/');
  const source = path.join(base, rel + '.lean');
  const output = path.join(base, '.lake/build/lib/lean', rel + '.olean');
  const current = fs.existsSync(output) && fs.statSync(output).mtimeMs >= fs.statSync(source).mtimeMs;
  if (module.startsWith('Mathlib.') && current) return;
  const content = fs.readFileSync(source, 'utf8');
  for (const match of content.matchAll(/^(?:public )?import (.+)$/gm)) {
    for (const dep of match[1].split(/\s+/)) {
      if (!/^[A-Za-z_][A-Za-z0-9_.]*$/.test(dep)) break;
      visit(dep);
    }
  }
  // Lake still checks dependency traces of all requested upstream modules.
  if (!current || requested.includes(module)) pending.push(module);
}
requested.forEach(visit);
const stamp = new Date().toISOString().replaceAll(':', '-');
const logPath = path.join(root, 'audit', `serial-upstream-${stamp}.log`);
fs.mkdirSync(path.dirname(logPath), { recursive: true });
const log = fs.createWriteStream(logPath, { flags: 'wx' });
console.log(`Checking ${pending.length} targets serially. Log: ${logPath}`);
for (const [i, module] of pending.entries()) {
  console.log(`[${i + 1}/${pending.length}] ${module}`);
  log.write(`\nTARGET ${module}\n`);
  let recent = '';
  const child = spawn('lake', ['--no-cache', 'build', module], {
    cwd: root, stdio: ['ignore', 'pipe', 'pipe'],
  });
  for (const stream of [child.stdout, child.stderr]) stream.on('data', data => {
    log.write(data);
    recent = (recent + data.toString()).slice(-20000);
  });
  const code = await new Promise((resolve, reject) => {
    child.on('error', reject);
    child.on('close', resolve);
  });
  if (code !== 0) {
    const firstError = recent.indexOf('\nerror:');
    console.error(recent.slice(firstError >= 0 ? firstError : -6000));
    log.end();
    process.exitCode = code ?? 1;
    break;
  }
  console.log(`PASS ${module}`);
}
log.end();
