// A source-level regression check, complementary to (not a replacement for)
// the Lean build, explicit theorem signatures, and transitive axiom audit.
import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const targets = [
  ['ShortRingAnchor/Proposition36VerifiedGinibre.lean', 'proposition36_cyclicShortRing_withoutBC12'],
  ['ShortRingAnchor/Proposition38/VerifiedGinibre.lean', 'proposition38_withoutBC12'],
];
for (const [file, name] of targets) {
  const text = fs.readFileSync(path.join(root, file), 'utf8');
  const declaration = text.match(new RegExp(`^theorem ${name}\\b([\\s\\S]*?) := by`, 'm'));
  if (!declaration) throw new Error(`Missing explicit endpoint signature: ${name}`);
  const signature = declaration[1];
  for (const forbidden of ['BC12GinibreNegativeMomentTightness', 'GinibreProjectionIntegralFormula',
    'GinibreCorrelationFormulas', 'hBC12Negative', 'hBC12Full']) {
    if (signature.includes(forbidden)) throw new Error(`BC12 premise reintroduced in ${name}: ${forbidden}`);
  }
  if (!signature.includes('hGinibre') || !signature.includes('HasLaw'))
    throw new Error(`The explicit Gaussian model specification is missing: ${name}`);
}
console.log('Both explicit endpoint signatures omit the former BC12 premises.');
