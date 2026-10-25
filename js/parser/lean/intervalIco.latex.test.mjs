/**
 * Finset/Set Ico (and Icc/Ioc/Ioo) → [a, b) etc., including multiline second bound.
 * Run: `node js/parser/lean/intervalIco.latex.test.mjs`
 */
import { compile } from '../lean.js';
import { Lean } from './base.js';

const L = Lean.classes;

let failed = 0;
function check(name, cond, detail = '') {
  if (!cond) {
    failed++;
    console.error(`FAIL ${name}${detail ? ': ' + detail : ''}`);
  } else {
    console.log(`ok   ${name}`);
  }
}

function find(n, pred, out = []) {
  if (!n || typeof n !== 'object') return out;
  if (pred(n)) out.push(n);
  for (const a of n.args || []) find(a, pred, out);
  return out;
}

{
  const tree = compile('lemma m : (i : ℕ) ∈ Finset.Ico a b := by sorry');
  const inn = find(tree, (n) => n instanceof L.Lean_in)[0];
  const lx = inn.toLatex({});
  check('inline Ico → [a, b)', /\\left\[a, b\\right\)/.test(lx), lx);
  check('inline peels (i : ℕ) → i', /\{i\} \\in/.test(lx) && !/:/.test(lx) && !/ℕ/.test(lx), lx);
}

{
  const tree = compile(`
lemma m : (i : ℕ) ∈ Finset.Ico (∑ t ∈ Finset.Iio k, d t)
    (∑ t ∈ Finset.Iic k, d t) := by sorry
`);
  const ind = find(tree, (n) => n instanceof L.LeanArgsIndented && n.splitIntervalOperands())[0];
  check('multiline mem splits', !!ind);
  const lx = ind.toLatex({});
  check('multiline Ico → [∑_< , ∑_≤ )', /\\left\[.*\\right\)/.test(lx) && !/Ico/.test(lx), lx);
  check('keeps Iio/Iic sum sugar', /t < k/.test(lx) && /t \\le k/.test(lx), lx);
}

{
  const tree = compile(`
lemma m : if (i : ℕ) ∈ Finset.Ico a
    b then j else 0 := by sorry
`);
  const ite = find(tree, (n) => n instanceof L.LeanIte)[0];
  const lx = ite.toLatex({});
  check('if multiline Ico', /\\in \{\\left\[a, b\\right\)\}/.test(lx) && !/Ico/.test(lx), lx);
  check('if peels (i : ℕ) → i', /\{i\} \\in/.test(lx) && !/ℕ/.test(lx), lx);
}

{
  for (const [ctor, needle] of [
    ['Icc', '\\left[a, b\\right]'],
    ['Ioc', '\\left(a, b\\right]'],
    ['Ioo', '\\left(a, b\\right)'],
  ]) {
    const tree = compile(`
lemma m : x ∈ Set.${ctor} a
    b := by sorry
`);
    const ind = find(tree, (n) => n instanceof L.LeanArgsIndented && n.splitIntervalOperands())[0];
    const lx = ind?.toLatex({}) ?? '';
    check(`multiline ${ctor}`, lx.includes(needle) && !lx.includes(ctor), lx);
  }
}

{
  const tree = compile('lemma m : ∑ t ∈ Finset.Iio k, d t = 0 := by sorry');
  const s = find(tree, (n) => n instanceof L.Lean_sum)[0];
  check('∑ Iio unchanged', /\\sum\\limits_\{t < k\}/.test(s.toLatex({})), s.toLatex({}));
}

if (failed) {
  console.error(`${failed} failure(s)`);
  process.exit(1);
}
console.log('all ok');
