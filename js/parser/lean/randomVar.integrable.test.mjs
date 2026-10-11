/**
 * RV `r` inside `Integrable (fun ω ↦ G (r ω)) π` must be red when `π` is only
 * `[IsFiniteMeasure π]` (no `IsProbabilityMeasure` / `PSpace`).
 * Run: `node js/parser/lean/randomVar.integrable.test.mjs`
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

/** Signature mirrors Lemma/Random/MEqExpectS/of/CondIndep/Integrable/MeasurableJoint/Measurable.lean */
const src = `
open MeasureTheory ProbabilityTheory
lemma integrable_rv_in_fun
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
  {π : Measure Ω} [IsFiniteMeasure π]
  {r : Ω → β}
  {a : Ω → γ}
  {s : Ω → δ}
  {G : β → ℝ}
-- given
  (hG : Measurable G)
  (hr : Measurable (r, a, s))
  (h₄ : Integrable (fun ω ↦ G (r ω)) π)
  (h₅ : r ⟂ᵢ[π] a | s) :
-- imply
  True := by
  sorry
`;

const codes = compile(src).render2vue(false);
const given = codes.lemma[0].given ?? [];
const h4 = given.find((g) => (g.lean ?? '').includes('Integrable'));
const latex = h4?.latex ?? '';

check('found Integrable given hyp', !!h4, given.map((g) => g.lean).join(' | '));
check(
  'r inside Integrable fun is red',
  /\\color\{red\}\s*\{r\}/.test(latex) || latex.includes('{\\color{red} {r}}'),
  latex,
);
check(
  'omega stays uncolored as binder',
  !/\\color\{red\}\s*\{ω\}/.test(latex),
  latex,
);

// Full lemma file smoke (same hyp line)
import fs from 'fs';
const full = fs.readFileSync(
  'Lemma/Random/MEqExpectS/of/CondIndep/Integrable/MeasurableJoint/Measurable.lean',
  'utf8',
);
const fullGiven = compile(full).render2vue(false).lemma[0].given ?? [];
const fullH4 = fullGiven.find((g) => (g.lean ?? '').includes('Integrable'));
const fullLatex = fullH4?.latex ?? '';
check(
  'Measurable.lean h₄: r red inside fun',
  fullLatex.includes('{\\color{red} {r}}'),
  fullLatex,
);

if (failed) {
  console.error(`${failed} failure(s)`);
  process.exit(1);
}
console.log('all ok');
