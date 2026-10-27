/**
 * `@ᵒ` is one infix. Reprinting it as `@ ᵒ` is not the operator, and Lean reports
 * `expected token` on the superscript.
 * Run: `node js/parser/lean/outerProd.latex.test.mjs`
 */
import { compile } from '../lean.js';
import fs from 'fs';

let failed = 0;
function check(name, cond, detail = '') {
  if (!cond) {
    failed++;
    console.error(`FAIL ${name}${detail ? ': ' + detail : ''}`);
  } else {
    console.log(`ok   ${name}`);
  }
}

{
  const src = 'lemma m : (hM : (1 + r) • (p ᵥ* (A + b @ᵒ l)) = p) := by sorry';
  const out = String(compile(src));
  check('glued @ᵒ', out.includes('b @ᵒ l'), out);
  check('no split @ ᵒ', !out.includes('@ ᵒ'), out);
}

{
  const out = String(compile('lemma m : b @ l = 0 := by sorry'));
  check('plain @ stays', out.includes('b @ l') && !out.includes('@ᵒ'), out);
}

{
  const p = 'Lemma/Matrix/Any_And_EqSMul_UpdateCol/of/IsIrreducibleUpdateColAdd_Dot/LtDot_Add_SMul/EqSMul/All_Gt_0.lean';
  const lem = compile(fs.readFileSync(p, 'utf8')).render2vue(false).lemma[0];
  const hM = lem.given.map((g) => g.lean).join('\n');
  check('hM keeps @ᵒ', hM.includes('b @ᵒ l'), hM);
  check('hM not split', !hM.includes('@ ᵒ'), hM);
}

if (failed) process.exit(1);
console.log('all ok');
