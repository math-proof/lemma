/**
 * `gaussianReal μ σ` renders as glued `\mathcal{N}(μ, σ)`; `x ∼[π] μ` parses as LeanDistributed (HasLaw).
 * Run: `node js/parser/lean/distributed.gaussian.test.mjs`
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

/** Sympy single atom: `\mathcal{N}` immediately followed by `\left(`, not `{{\mathcal{N}}}` or a KaTeX space. */
function checkGlued(name, latex) {
  check(`${name} mathcal`, /\\mathcal\{N\}/.test(latex), latex);
  check(`${name} no raw unicode`, !latex.includes('𝒩'), latex);
  check(`${name} glued left`, /\\mathcal\{N\}\\left\(/.test(latex), latex);
  check(`${name} not wrapped atom`, !/\{\\mathcal\{N\}\}/.test(latex), latex);
  check(`${name} no space after N`, !/\\mathcal\{N\}[ {]/.test(latex) && !/\\mathcal\{N\}\\ /.test(latex), latex);
}

{
  const src = 'lemma m : gaussianReal μ₀ σ₀ = μ := by sorry';
  const ast = compile(src);
  const str = String(ast);
  check('gaussianReal spaced', str.includes('gaussianReal μ₀ σ₀'), JSON.stringify(str));
  check('gaussianReal not call-paren', !str.includes('gaussianReal('), JSON.stringify(str));
  checkGlued('bare app', ast.render2vue(false).lemma[0].imply.latex);
}

{
  const src = 'lemma m : gaussianReal μ₀ σ₀² = μ := by sorry';
  const latex = compile(src).render2vue(false).lemma[0].imply.latex;
  checkGlued('variance square', latex);
  check('variance square keeps ^2', /\^2/.test(latex), latex);
}

{
  const src = 'lemma m : gaussianReal = μ := by sorry';
  const latex = compile(src).render2vue(false).lemma[0].imply.latex;
  check('bare token mathcal', /\\mathcal\{N\}/.test(latex), latex);
  check('bare token no identifier', !latex.includes('gaussianReal'), latex);
}

{
  const src = 'lemma m : x ∼[π] μ := by sorry';
  const m = compile(src);
  const str = String(m);
  check('∼[π] str', str.includes('x ∼[π] μ'), JSON.stringify(str));
  const latex = m.render2vue(false).lemma[0].imply.latex;
  check('∼[π] latex sim', /\\sim/.test(latex), latex);
  check('∼[π] latex red x', /\\color\{red\}/.test(latex), latex);
  check('∼[π] no GetElem tilde', !/∼_\{π\}/.test(latex) && !latex.includes('{∼}'), latex);
}

{
  const src = 'lemma m : x ∼[π] gaussianReal μ₀ σ₀ := by sorry';
  const m = compile(src);
  const str = String(m);
  check('combo str', str.includes('x ∼[π] gaussianReal μ₀ σ₀'), JSON.stringify(str));
  const latex = m.render2vue(false).lemma[0].imply.latex;
  checkGlued('combo', latex);
  check('combo sim', /\\sim/.test(latex), latex);
}

{
  const src = 'lemma m : x ⟂ᵢ[π] y := by sorry';
  const latex = compile(src).render2vue(false).lemma[0].imply.latex;
  check('perp intact', /\\perp/.test(latex) && /\\color\{red\}/.test(latex), latex);
}

{
  const src = 'lemma m : α ≃ β := by sorry';
  const latex = compile(src).render2vue(false).lemma[0].imply.latex;
  check('simeq intact', /\\simeq/.test(latex), latex);
}

{
  // given-column path (hyp under LeanDistributed) must match imply: glued \mathcal{N}, no raw unicode
  const src = `lemma m
  (h₁ : x ∼[π] gaussianReal μ₀ σ₀²) :
  y ∼[π] gaussianReal (μ₀ + μ₁) (σ₀² + σ₁²) := by sorry`;
  const vue = compile(src).render2vue(false).lemma[0];
  const gLatex = (vue.given || []).map((g) => g.latex).join('\n');
  const iLatex = vue.imply?.latex || '';
  checkGlued('given', gLatex);
  checkGlued('imply', iLatex);
  check('given keeps variance square', /\^2/.test(gLatex), gLatex);
  check('imply peels sums', /\\mathcal\{N\}\\left\([^)]*\+/.test(iLatex), iLatex);
  check('given lean str spaced', (vue.given || []).every((g) => String(g.lean).includes('gaussianReal μ₀ σ₀²')), JSON.stringify(vue.given));
  check('given lean not call-paren', (vue.given || []).every((g) => !String(g.lean).includes('gaussianReal(')), JSON.stringify(vue.given));
}

{
  // Sum / prod binders stay black under ∼; the summand head `x` stays red.
  // `∑ k : Fin n` prints as `\sum_{k < n}` (DistributedSum imply shape).
  const src = `lemma m
  (h₁ : (∑ k : Fin n, x k) ∼[π] gaussianReal (∑ k : Fin n, μ k) (∑ k : Fin n, (σ k) ^ 2)) :
  (∑ k : Fin n, x k) ∼[π] gaussianReal (∑ k : Fin n, μ k) (∑ k : Fin n, (σ k) ^ 2) := by sorry`;
  const vue = compile(src).render2vue(false).lemma[0];
  const imply = vue.imply?.latex || '';
  const given = (vue.given || []).map((g) => g.latex).join('\n');
  const redK = /\\color\{red\}\s*\{k\}/;
  const redX = /\\color\{red\}\s*\{x\}/;
  check('imply sum binder k not red', !redK.test(imply), imply);
  check('imply summand x red', redX.test(imply), imply);
  check('given sum binder k not red', !redK.test(given), given);
  check('given summand x red', redX.test(given), given);
  const law = imply.split('\\sim').slice(1).join('\\sim');
  check('imply law side not red', law.length > 0 && !/\\color\{red\}/.test(law), law);
}

{
  const forms = [
    ['lt', '(∑ k < n, x k)'],
    ['univ', '(∑ k ∈ Finset.univ, x k)'],
    ['prod', '(∏ k : Fin n, x k)'],
  ];
  for (const [name, lhs] of forms) {
    const latex = compile(`lemma m : ${lhs} ∼[π] gaussianReal μ σ := by sorry`)
      .render2vue(false).lemma[0].imply.latex;
    check(`${name} binder k not red`, !/\\color\{red\}\s*\{k\}/.test(latex), latex);
    check(`${name} summand x red`, /\\color\{red\}\s*\{x\}/.test(latex), latex);
    if (name === 'lt')
      check('lt bound n not red', !/\\color\{red\}\s*\{n\}/.test(latex), latex);
  }
}

if (failed) {
  console.error(`\n${failed} failure(s)`);
  process.exit(1);
}
console.log('\nall ok');
