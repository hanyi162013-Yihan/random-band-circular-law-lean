// Build the copied dependency closure serially, using only local sources.
// No cache downloads, package updates, deletion, or other-project mutation.
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';
import { createHash } from 'node:crypto';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const requested = process.argv.slice(2);
if (!requested.length) throw new Error('Supply the Lean module targets to check.');
const sha256 = data => createHash('sha256').update(data).digest('hex');
const configuration = sha256(['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']
  .map(file => fs.readFileSync(path.join(root, file), 'utf8')).join('\n'));
const stampFile = path.join(root, '.lake/build/serial-source-hashes.json');
let checkedSources = {};
try {
  const saved = JSON.parse(fs.readFileSync(stampFile, 'utf8'));
  if (saved.configuration === configuration) checkedSources = saved.modules ?? {};
} catch { /* A first build has no successful-source inventory yet. */ }
const sourceHashes = new Map();
const seen = new Set();
const dirty = new Map();
const pending = [];
function visit(module) {
  if (seen.has(module)) return dirty.get(module) ?? false;
  seen.add(module);
  if (module === 'Mathlib') throw new Error('Refusing an umbrella Mathlib build.');
  let base;
  if (module === 'Vendor' || module === 'ShortRingAnchor' || module.startsWith('Vendor.') || module.startsWith('ShortRingAnchor.')) base = root;
  else if (module === 'Ginibre' || module.startsWith('Ginibre.')) base = path.join(root, '.lake/packages/GinibreCorrelationIdentities');
  else if (module.startsWith('Mathlib.')) base = path.join(root, '.lake/packages/mathlib');
  else return; // The already installed auxiliary packages are managed by Lake.
  const rel = module.replaceAll('.', '/');
  const source = path.join(base, rel + '.lean');
  const output = path.join(base, '.lake/build/lib/lean', rel + '.olean');
  // Checkout and cache extraction times need not agree. Leave validation of
  // existing pinned mathlib artifacts to Lake's dependency traces; do not
  // schedule thousands of redundant per-module prebuilds based on mtimes.
  if (module.startsWith('Mathlib.') && fs.existsSync(output)) return false;
  const content = fs.readFileSync(source, 'utf8');
  const hash = sha256(content);
  sourceHashes.set(module, hash);
  // Git checkouts give unchanged sources fresh mtimes. A stamp is issued
  // only AFTER a successful Lake build below, and changed dependencies
  // still propagate through `visit`. This only avoids redundant serial
  // invocations; the requested targets and final normal build continue
  // to validate Lake's complete dependency traces.
  const current = fs.existsSync(output) && checkedSources[module] === hash;
  let needsBuild = !current;
  for (const match of content.matchAll(/^(?:public )?import (.+)$/gm)) {
    for (const dep of match[1].split(/\s+/)) {
      if (!/^[A-Za-z_][A-Za-z0-9_.]*$/.test(dep)) break;
      if (visit(dep)) needsBuild = true;
    }
  }
  // Lake still checks dependency traces of all requested upstream modules.
  if (needsBuild || requested.includes(module)) pending.push(module);
  dirty.set(module, needsBuild);
  return needsBuild;
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
  checkedSources[module] = sourceHashes.get(module);
  fs.mkdirSync(path.dirname(stampFile), { recursive: true });
  fs.writeFileSync(stampFile, JSON.stringify({ configuration, modules: checkedSources }) + '\n');
  console.log(`PASS ${module}`);
}
log.end();
