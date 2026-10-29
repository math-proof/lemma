/**
 * `𝒩(μ, σ)` stays glued; `x ∼[π] μ` parses as LeanDistributed (HasLaw).
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

{
  const src = 'lemma m : 𝒩(μ₀, σ₀) = μ := by sorry';
  const ast = compile(src);
  const str = String(ast);
  check('𝒩( no space', str.includes('𝒩(μ₀, σ₀)'), JSON.stringify(str));
  check('𝒩( not spaced', !str.includes('𝒩 ('), JSON.stringify(str));
  const latex = ast.render2vue(false).lemma[0].imply.latex;
  check('𝒩 mathcal', /\\mathcal\{N\}/.test(latex), latex);
  check('𝒩 not raw unicode in latex', !latex.includes('𝒩'), latex);
  check('𝒩 sympy glue', /\\mathcal\{N\}(\\colorbox|\{)/.test(latex), latex);
  check('𝒩 not wrapped atom', !/\{\\mathcal\{N\}\}/.test(latex), latex);
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
  const src = 'lemma m : x ∼[π] 𝒩(μ₀, σ₀) := by sorry';
  const str = String(compile(src));
  check('combo str', str.includes('x ∼[π] 𝒩(μ₀, σ₀)'), JSON.stringify(str));
  check('combo no 𝒩 space', !str.includes('𝒩 ('), JSON.stringify(str));
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
  (h₁ : x ∼[π] 𝒩(μ₀, σ₀)) :
  y ∼[π] 𝒩(μ₀ + μ₁, σ₀ + σ₁) := by sorry`;
  const vue = compile(src).render2vue(false).lemma[0];
  const gLatex = (vue.given || []).map((g) => g.latex).join('\n');
  const iLatex = vue.imply?.latex || '';
  check('given has mathcal', /\\mathcal\{N\}/.test(gLatex), gLatex);
  check('imply has mathcal', /\\mathcal\{N\}/.test(iLatex), iLatex);
  check('given no raw 𝒩', !gLatex.includes('𝒩'), gLatex);
  check('imply no raw 𝒩', !iLatex.includes('𝒩'), iLatex);
  // sympy-style single atom: \mathcal{N} then colorbox/group, not {\mathcal{N}}{...}
  check('given sympy mathcal glue', /\\mathcal\{N\}(\\colorbox|\{)/.test(gLatex), gLatex);
  check('imply sympy mathcal glue', /\\mathcal\{N\}(\\colorbox|\{)/.test(iLatex), iLatex);
  check('given not wrapped N atom', !/\{\\mathcal\{N\}\}/.test(gLatex), gLatex);
  check('imply not wrapped N atom', !/\{\\mathcal\{N\}\}/.test(iLatex), iLatex);
  check('given lean str glued', (vue.given || []).every((g) => !String(g.lean).includes('𝒩 (')), JSON.stringify(vue.given));
}

if (failed) {
  console.error(`\n${failed} failure(s)`);
  process.exit(1);
}
console.log('\nall ok');
