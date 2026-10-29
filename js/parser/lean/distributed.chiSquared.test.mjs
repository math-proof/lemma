/**
 * `chiSquaredReal n` renders as glued `\mathcal{X}^{2}(n)`; `x ∼[π] μ` parses as LeanDistributed (HasLaw).
 * Run: `node js/parser/lean/distributed.chiSquared.test.mjs`
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

/** Sympy single atom: `\mathcal{X}^{2}` immediately followed by `\left(`, not a spaced function name. */
function checkGlued(name, latex) {
  check(`${name} mathcal`, /\\mathcal\{X\}\^\{2\}/.test(latex), latex);
  check(`${name} no identifier`, !latex.includes('chiSquaredReal'), latex);
  check(`${name} glued left`, /\\mathcal\{X\}\^\{2\}\\left\(/.test(latex), latex);
  check(`${name} not wrapped atom`, !/\{\\mathcal\{X\}\^\{2\}\}/.test(latex), latex);
  check(`${name} no space after square`, !/\\mathcal\{X\}\^\{2\}[ {]/.test(latex) && !/\\mathcal\{X\}\^\{2\}\\ /.test(latex), latex);
}

{
  const src = 'lemma m : chiSquaredReal n = μ := by sorry';
  const ast = compile(src);
  const str = String(ast);
  check('chiSquaredReal spaced', str.includes('chiSquaredReal n'), JSON.stringify(str));
  check('chiSquaredReal not call-paren', !str.includes('chiSquaredReal('), JSON.stringify(str));
  const latex = ast.render2vue(false).lemma[0].imply.latex;
  checkGlued('bare app', latex);
  check('bare app degree', /\\mathcal\{X\}\^\{2\}\\left\(n\\right\)/.test(latex), latex);
}

{
  const src = 'lemma m : chiSquaredReal n₀ = μ := by sorry';
  const latex = compile(src).render2vue(false).lemma[0].imply.latex;
  checkGlued('subscript degree', latex);
  check('subscript degree keeps n_0', /\\mathcal\{X\}\^\{2\}\\left\(n_\{0\}\\right\)/.test(latex), latex);
}

{
  const src = 'lemma m : chiSquaredReal (n + k) = μ := by sorry';
  const latex = compile(src).render2vue(false).lemma[0].imply.latex;
  checkGlued('paren sum', latex);
  check('paren sum peels', /\\mathcal\{X\}\^\{2\}\\left\([^)]*\+/.test(latex), latex);
  check('paren sum no colorbox', !/colorbox/.test(latex), latex);
}

{
  const src = 'lemma m : chiSquaredReal (Fintype.card ι) = μ := by sorry';
  const latex = compile(src).render2vue(false).lemma[0].imply.latex;
  checkGlued('qualified degree', latex);
  check('qualified degree card bars', /\\mathcal\{X\}\^\{2\}\\left\(\\left\|\{ι\}\\right\|\\right\)/.test(latex), latex);
}

{
  const src = 'lemma m : chiSquaredReal = μ := by sorry';
  const latex = compile(src).render2vue(false).lemma[0].imply.latex;
  check('bare token mathcal', /\\mathcal\{X\}\^\{2\}/.test(latex), latex);
  check('bare token no identifier', !latex.includes('chiSquaredReal'), latex);
  check('bare token no paren', !/\\left\(/.test(latex), latex);
}

{
  const src = 'lemma m : x ∼[π] chiSquaredReal n := by sorry';
  const m = compile(src);
  const str = String(m);
  check('combo str', str.includes('x ∼[π] chiSquaredReal n'), JSON.stringify(str));
  const latex = m.render2vue(false).lemma[0].imply.latex;
  checkGlued('combo', latex);
  check('combo sim', /\\sim/.test(latex), latex);
  check('combo red x', /\\color\{red\}/.test(latex), latex);
}

{
  const src = 'lemma m : HasLaw x (chiSquaredReal n) π := by sorry';
  const latex = compile(src).render2vue(false).lemma[0].imply.latex;
  checkGlued('HasLaw', latex);
  check('HasLaw keeps outer paren', /\\left\(\\mathcal\{X\}\^\{2\}\\left\(n\\right\)\\right\)/.test(latex), latex);
}

{
  // given-column path (hyp under LeanDistributed) must match imply: glued \mathcal{X}^{2}
  const src = `lemma m
  (h₁ : x ∼[π] chiSquaredReal n) :
  y ∼[π] chiSquaredReal (n + k) := by sorry`;
  const vue = compile(src).render2vue(false).lemma[0];
  const gLatex = (vue.given || []).map((g) => g.latex).join('\n');
  const iLatex = vue.imply?.latex || '';
  checkGlued('given', gLatex);
  checkGlued('imply', iLatex);
  check('given degree n', /\\mathcal\{X\}\^\{2\}\\left\(n\\right\)/.test(gLatex), gLatex);
  check('imply peels sum', /\\mathcal\{X\}\^\{2\}\\left\([^)]*\+/.test(iLatex), iLatex);
  check('given lean str spaced', (vue.given || []).every((g) => String(g.lean).includes('chiSquaredReal n')), JSON.stringify(vue.given));
  check('given lean not call-paren', (vue.given || []).every((g) => !String(g.lean).includes('chiSquaredReal(')), JSON.stringify(vue.given));
}

{
  // Sum of squares has law chiSquaredReal n: binder stays black, summand head stays red, law is not red.
  const src = `lemma m
  (h₁ : (∑ k : Fin n, (x k) ^ 2) ∼[π] chiSquaredReal n) :
  (∑ k : Fin n, (x k) ^ 2) ∼[π] chiSquaredReal n := by sorry`;
  const vue = compile(src).render2vue(false).lemma[0];
  const imply = vue.imply?.latex || '';
  const given = (vue.given || []).map((g) => g.latex).join('\n');
  const redK = /\\color\{red\}\s*\{k\}/;
  const redX = /\\color\{red\}\s*\{x\}/;
  checkGlued('sq imply', imply);
  checkGlued('sq given', given);
  check('imply sum binder k not red', !redK.test(imply), imply);
  check('imply summand x red', redX.test(imply), imply);
  check('given sum binder k not red', !redK.test(given), given);
  check('given summand x red', redX.test(given), given);
  const law = imply.split('\\sim').slice(1).join('\\sim');
  check('imply law side not red', law.length > 0 && !/\\color\{red\}/.test(law), law);
}

if (failed) {
  console.error(`\n${failed} failure(s)`);
  process.exit(1);
}
console.log('\nall ok');
