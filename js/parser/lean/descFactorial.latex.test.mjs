/**
 * `c₀ * h[k]` and `B * n.descFactorial e` must not juxtapose into one symbol.
 * Run: `node js/parser/lean/descFactorial.latex.test.mjs`
 */
import { compile } from '../lean.js';
import fs from 'fs';

const p = 'Lemma/Complex/Any_Any_All_Eq_AddAddAddMul_PowMulMul_DescFactorialPow_SubMulMul_DescFactorialPow_SubMulMul_DescFactorialPow_Sub/of/All_EqAdd_4_AddAddAddMulMul_Add_1Mul_Add_2Mul_Add_3.lean';
const lem = compile(fs.readFileSync(p, 'utf8')).render2vue(false).lemma[0];
const given = lem.given[0].latex;
const imply = lem.imply.latex;

let failed = 0;
function check(name, cond, detail = '') {
  if (!cond) {
    failed++;
    console.error(`FAIL ${name}${detail ? ': ' + detail : ''}`);
  } else {
    console.log(`ok   ${name}`);
  }
}

check('given c₀ · h_k', /c_\{0\} \\cdot \{h\}_\{k\}/.test(given), given);
check('imply falling factorial', /\{n\}\^\{\\underline\{e\}\}/.test(imply), imply);
check('imply B · falling', /B \\cdot \{n\}\^\{\\underline\{e\}\}/.test(imply), imply);
check('single letters still juxtapose', (() => {
  const lx = compile('lemma m : b * x = 0 := by sorry').render2vue(false).lemma[0].imply.latex;
  return /\{b\s+x\}/.test(lx) && !/\\cdot/.test(lx);
})());

if (failed) process.exit(1);
console.log('all ok');
