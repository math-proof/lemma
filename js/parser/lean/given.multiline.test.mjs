/**
 * Multiline `(h : StronglyMeasurable\n  (fun …))` must stay one given with its own LaTeX;
 * the following `(hMs : …)` must not steal that slot.
 * Run: `node js/parser/lean/given.multiline.test.mjs`
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

const multi = `
open MeasureTheory
@[path]
private lemma main
  {Θ S A : Type*} {M : Θ → S → A → ℝ} {θ : Θ} {Ms : ℝ}
-- given
  (h₆ : ∀ x, True)
  (hφ : StronglyMeasurable
    (fun z : S × A => ∇[θ] Real.log (M θ z.1 z.2)))
  (hMs : ∀ y u, ‖∇[θ] Real.log (M θ y u)‖ ≤ Ms) :
  True := by
  trivial
`;

const single = `
open MeasureTheory
@[path]
private lemma main
  {Θ S A : Type*} {M : Θ → S → A → ℝ} {θ : Θ} {Ms : ℝ}
-- given
  (h₆ : ∀ x, True)
  (hφ : StronglyMeasurable (fun z : S × A => ∇[θ] Real.log (M θ z.1 z.2)))
  (hMs : ∀ y u, ‖∇[θ] Real.log (M θ y u)‖ ≤ Ms) :
  True := by
  trivial
`;

function slots(src) {
  return (compile(src).render2vue(false).lemma[0].given ?? []).map((g) => ({
    lean: (g.lean ?? '').replace(/\s+/g, ' ').trim(),
    latex: (g.latex ?? '').replace(/\s+/g, ' ').trim(),
    tag: /\\tag\*\{\$([^$]+)\$\}/.exec(g.latex ?? '')?.[1] ?? '',
  }));
}

{
  const g = slots(multi);
  check('multiline count=3', g.length === 3, `got ${g.length}: ${g.map((x) => x.tag || x.lean.slice(0, 20)).join(' | ')}`);
  check('slot0 is h₆', g[0]?.tag === 'h₆' || g[0]?.lean.includes('h₆'), g[0]?.lean);
  check('slot1 lean is hφ', g[1]?.lean.includes('hφ') && g[1]?.lean.includes('StronglyMeasurable'), g[1]?.lean);
  check('slot1 latex is StronglyMeasurable (not hMs ∀)', /StronglyMeasurable/.test(g[1]?.latex ?? '') && !/\\\\forall.*y/.test(g[1]?.latex ?? ''), g[1]?.latex?.slice(0, 120));
  check('slot1 tag hφ', g[1]?.tag === 'hφ', g[1]?.tag);
  check('slot2 lean is hMs', g[2]?.lean.includes('hMs'), g[2]?.lean);
  check('slot2 tag hMs', g[2]?.tag === 'hMs', g[2]?.tag);
}

{
  const g = slots(single);
  check('single-line count=3', g.length === 3, `got ${g.length}`);
  check('single-line hφ latex ok', /StronglyMeasurable/.test(g[1]?.latex ?? ''), g[1]?.latex?.slice(0, 80));
  check('single-line hMs tag', g[2]?.tag === 'hMs', g[2]?.tag);
}

{
  const f =
    'Lemma/Random/GradExpectDotPow_Id/eq/ExpectDot_SMul_GradLogProbCond/of/GtInftySup/All_Differentiable_Prob/All_Integrable/All_LeNormGrad/All_Eq_Joint/All_EqWithDensity/In_Icc/In_Ico.lean';
  const g = slots(fs.readFileSync(f, 'utf8'));
  const hphi = g.find((x) => x.lean.includes('hφ') || x.tag === 'hφ');
  const hMs = g.find((x) => x.lean.includes('hMs') || x.tag === 'hMs');
  check('In_Ico: has hφ given', !!hphi, `count=${g.length} tags=${g.map((x) => x.tag).join(',')}`);
  check('In_Ico: hφ latex is StronglyMeasurable', /StronglyMeasurable/.test(hphi?.latex ?? ''), hphi?.latex?.slice(0, 120));
  check('In_Ico: has separate hMs', !!hMs && hMs !== hphi, hMs?.lean?.slice(0, 60));
  check('In_Ico: hMs latex is forall/norm', /\\\\forall|\\\\left\\\\lVert|∀|∥/.test(hMs?.latex ?? '') || (hMs?.latex ?? '').includes('Ms'), hMs?.latex?.slice(0, 120));
}

if (failed) {
  console.error(`${failed} failure(s)`);
  process.exit(1);
}
console.log('all ok');
