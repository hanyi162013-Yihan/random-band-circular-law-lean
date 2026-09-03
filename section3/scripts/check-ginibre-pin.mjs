import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
const revision = '403bab996ebc6b8331531bdf12b7a8c84bf61a4d';
for (const dir of ['', 'section3', 'section5', 'section6']) {
  const file = path.join(root, dir, 'lake-manifest.json');
  const matches = JSON.parse(fs.readFileSync(file, 'utf8')).packages
    .filter(p => p.name === 'GinibreCorrelationIdentities');
  if (matches.length !== 1 || matches[0].rev !== revision || matches[0].inputRev !== revision)
    throw new Error(`Missing or inconsistent Ginibre proof pin: ${file}`);
  if (matches[0].inherited !== ['section5', 'section6'].includes(dir))
    throw new Error(`Incorrect dependency inheritance: ${file}`);
}
console.log('All four project manifests agree on the pinned Ginibre proof dependency.');
