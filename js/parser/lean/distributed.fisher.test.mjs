/**
 * `fisherReal d₁ d₂` renders as glued `\mathrm{F}(d₁, d₂)` (upright Fisher F).
 * Run: `node js/parser/lean/distributed.fisher.test.mjs`
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

/** Sympy-style single atom: `\mathrm{F}` immediately followed by `\left(`. */
function checkGlued(name, latex) {
  check(`${name} mathrm F`, /\\mathrm\{F\}/.test(latex), latex);
  check(`${name} no identifier`, !latex.includes('fisherReal'), latex);
  check(`${name} glued left`, /\\mathrm\{F\}\\left\(/.test(latex), latex);
  check(`${name} not wrapped atom`, !/\{\\mathrm\{F\}\}/.test(latex), latex);
  check(`${name} no space after F`, !/\\mathrm\{F\}[ {]/.test(latex) && !/\\mathrm\{F\}\\ /.test(latex), latex);
}

{
  const src = 'lemma m : fisherReal n m = μ := by sorry';
  const ast = compile(src);
  const str = String(ast);
  check('fisherReal spaced', str.includes('fisherReal n m'), JSON.stringify(str));
  check('fisherReal not call-paren', !str.includes('fisherReal('), JSON.stringify(str));
  const latex = ast.render2vue(false).lemma[0].imply.latex;
  checkGlued('bare app', latex);
  check('bare app degrees', /\\mathrm\{F\}\\left\(n, m\\right\)/.test(latex), latex);
}

{
  const src = 'lemma m : fisherReal n₀ m₀ = μ := by sorry';
  const latex = compile(src).render2vue(false).lemma[0].imply.latex;
  checkGlued('subscript degrees', latex);
  check('subscript keeps n_0 m_0', /\\mathrm\{F\}\\left\(n_\{0\}, m_\{0\}\\right\)/.test(latex), latex);
}

{
  const src = 'lemma m : fisherReal (m - 1) (m * (n - 1)) = μ := by sorry';
  const latex = compile(src).render2vue(false).lemma[0].imply.latex;
  checkGlued('anova juxta', latex);
  check('anova peels first', /\\mathrm\{F\}\\left\([^,]*(?:-|−)/.test(latex), latex);
  check('anova peels second', /\\mathrm\{F\}\\left\(.+,.+\\right\)/.test(latex), latex);
  // colorbox on inner (n-1) is normal juxta-mul render, not a fisher glue issue
  check('anova keeps mul structure', /m/.test(latex) && /n/.test(latex), latex);
  check('anova no identifier', !latex.includes('fisherReal'), latex);
}

{
  const src = 'lemma m : fisherReal = μ := by sorry';
  const latex = compile(src).render2vue(false).lemma[0].imply.latex;
  check('bare token mathrm', /\\mathrm\{F\}/.test(latex), latex);
  check('bare token no identifier', !latex.includes('fisherReal'), latex);
  check('bare token no paren', !/\\left\(/.test(latex), latex);
}

{
  const src = 'lemma m : x ∼[π] fisherReal (m - 1) (m * (n - 1)) := by sorry';
  const m = compile(src);
  const str = String(m);
  check('combo str', str.includes('x ∼[π] fisherReal (m - 1) (m * (n - 1))'), JSON.stringify(str));
  const latex = m.render2vue(false).lemma[0].imply.latex;
  checkGlued('combo', latex);
  check('combo sim', /\\sim/.test(latex), latex);
  check('combo red x', /\\color\{red\}/.test(latex), latex);
}

{
  const src = `lemma m
  (h₁ : x ∼[π] fisherReal d₁ d₂) :
  y ∼[π] fisherReal (m - 1) (m * (n - 1)) := by sorry`;
  const vue = compile(src).render2vue(false).lemma[0];
  const gLatex = (vue.given || []).map((g) => g.latex).join('\n');
  const iLatex = vue.imply?.latex || '';
  checkGlued('given', gLatex);
  checkGlued('imply', iLatex);
  check('given degrees', /\\mathrm\{F\}\\left\(/.test(gLatex), gLatex);
  check('given lean str spaced', (vue.given || []).every((g) => String(g.lean).includes('fisherReal d₁ d₂')), JSON.stringify(vue.given));
  check('given lean not call-paren', (vue.given || []).every((g) => !String(g.lean).includes('fisherReal(')), JSON.stringify(vue.given));
}

if (failed) {
  console.error(`\n${failed} failure(s)`);
  process.exit(1);
}
console.log('\nall ok');
