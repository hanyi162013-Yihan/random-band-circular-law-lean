// Read-only publication payload. No dependency directories or manuscripts.
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { fileURLToPath } from 'node:url';
const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
function collect(dir) {
  return fs.readdirSync(dir, { withFileTypes: true }).flatMap(e => {
    if (e.name.startsWith('.')) return [];
    const p = path.join(dir, e.name);
    return e.isDirectory() ? collect(p) : [p];
  });
}
const paths = [
  ...fs.readdirSync(root).filter(p => /\.md$|\.lean$/.test(p)),
  'lakefile.toml', 'lake-manifest.json', 'lean-toolchain', '.gitignore',
  ...['ShortRingAnchor', 'Vendor'].flatMap(d => collect(path.join(root, d))
    .map(p => path.relative(root, p)).filter(p => p.endsWith('.lean') || /^Vendor\/licenses\//.test(p))),
  ...fs.readdirSync(path.join(root, 'scripts')).filter(p => p.endsWith('.mjs')).map(p => 'scripts/' + p),
  ...['stieltjes-smoothing', 'matrix-stieltjes-build', 'matrix-stieltjes',
    'concrete-models-build', 'concrete-models'].map(p => `audit/${p}-2026-09-02.log`),
].sort();
if (new Set(paths).size !== paths.length) throw new Error('Duplicate publication path.');
const entries = paths.map(p => {
  let content = fs.readFileSync(path.join(root, p), 'utf8');
  // Replace workstation-only provenance prefixes, leaving source project and file names.
  content = content.replace(/\/Users\/[^/\s]+\/Documents\/Codex\/\d{4}-\d{2}-\d{2}\//g, 'upstream-sources/');
  if (/\/Users\/|\/private\/tmp\//.test(content)) throw new Error(`Private path remains in ${p}`);
  return { path: 'section3/' + p, mode: '100644', type: 'blob', content };
});
const manifest = entries.map(e => ({ path: e.path.slice(9), bytes: Buffer.byteLength(e.content),
  sha256: crypto.createHash('sha256').update(e.content).digest('hex') }));
entries.push({ path: 'section3/SOURCE_MANIFEST.json', mode: '100644', type: 'blob',
  content: JSON.stringify({ scope: 'Published source snapshot; hashes are not proof certificates.', files: manifest }, null, 2) + '\n' });
entries.push({ path: '.github/workflows/section3.yml', mode: '100644', type: 'blob',
  content: fs.readFileSync(path.join(root, 'ci/section3.yml'), 'utf8') });
const args = process.argv.slice(2);
if (args[0] === '--manifest') {
  console.log(JSON.stringify(entries.map(({ path, content }) => ({ path, bytes: Buffer.byteLength(content) }))));
} else {
  const index = Number(args[0] ?? 0), batches = []; let batch = [], size = 0;
  for (const e of entries) {
    const n = Buffer.byteLength(JSON.stringify(e));
    if (batch.length && size + n > 80000) { batches.push(batch); batch = []; size = 0; }
    batch.push(e); size += n;
  }
  if (batch.length) batches.push(batch);
  console.log(JSON.stringify({ index, batches: batches.length, entries: batches[index] ?? [] }));
}
