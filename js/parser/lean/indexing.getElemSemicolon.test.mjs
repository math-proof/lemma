/**
 * GetElem index with trailing `; measure` must round-trip: `cov[f, g; π]` not `cov[f, g π]`.
 * Run: `node js/parser/lean/indexing.getElemSemicolon.test.mjs`
 */
import { compile } from '../lean.js';

let failed = 0;
function check(name, cond, detail = '') {
  if (!cond) {
    failed++;
    console.error(`FAIL ${name}${detail ? ': ' + detail : ''}`);
  } else {
    console.log(`ok   ${name}`);
  }
}

const cases = [
  ['cov[f, g; pi]', 'cov[f, g; pi]'],
  ['a[i, j; mu]', 'a[i, j; mu]'],
  ['cov[f; pi]', 'cov[f; pi]'],
];

for (const [src, expect] of cases) {
  const out = String(compile(src + '\n')).trim();
  check(src + ' round-trip', out === expect, JSON.stringify(out));
  check(src + ' keeps ;', out.includes(';'), out);
}

const lemma = `lemma L (f g : Omega -> Real) (pi : Measure Omega) : cov[f, g; pi] = 0 := by
  sorry
`;
const lean = String(compile(lemma));
check('lemma imply keeps ; in cov', /cov\[f, g; pi\]/.test(lean), JSON.stringify(lean.slice(0, 200)));

if (failed) {
  console.error(`${failed} failure(s)`);
  process.exit(1);
}
console.log('all ok');
