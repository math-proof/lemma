/**
 * `max⁻¹[i] e`: `^{-1}` must be a top-right superscript (not an overscript).
 * Run: `node js/parser/lean/argmax.latex.test.mjs`
 */
import katex from 'katex';
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

const src = `
lemma main
  {n : ℕ} {f : ℕ → ℝ}
-- given
  (h : True) :
-- imply
  max⁻¹[i : ℕ | i < n] (f i) = min⁻¹[i : ℕ | i < n] (f i) := by
  sorry
`;

const latex = compile(src).render2vue(false).lemma[0].imply?.latex ?? '';
check(
  'uses underset + operatorname max^{-1}',
  latex.includes('\\underset{') && latex.includes('\\operatorname{max}^{-1}'),
  latex,
);
check(
  'uses underset + operatorname min^{-1}',
  latex.includes('\\operatorname{min}^{-1}'),
  latex,
);
check('no \\limits on max^{-1}', !/max\^{-1}[^}]*\\limits/.test(latex) && !latex.includes('\\max^{-1}\\limits'), latex);
check('no mathop{\\max^{-1}}', !latex.includes('\\mathop{\\max^{-1}}'), latex);

// KaTeX: -1 must be an msupsub (side script), not only an op-limits overscript.
const fragment = String.raw`\underset{i}{\operatorname{max}^{-1}}`;
const html = katex.renderToString(fragment, { throwOnError: true, displayMode: true });
check('KaTeX keeps side superscript (msupsub)', html.includes('msupsub'), html.slice(0, 200));

if (failed) {
  console.error(`${failed} failure(s)`);
  process.exit(1);
}
console.log('all ok');
console.log('SAMPLE:', latex);
