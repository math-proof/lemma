/**
 * Fun-indexed RVs `{s : ℕ ⇀ Ω → S}` must paint value-position heads red (`V[t] s[t]`),
 * while `{V : ℕ ⇀ S → ℝ}` / `{Q : ℕ ⇀ S → A → ℝ}` stay unpainted.
 * Run: `node js/parser/lean/randomVar.funIndex.test.mjs`
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

/** Signature mirrors Lemma/Random/MEq_Expect/…/All_MeasurableJoint/In_Ico.lean */
const src = `
open MeasureTheory ProbabilityTheory Random
lemma fun_index_rv_value
  [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace S] [MeasurableSpace A]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ ⇀ Ω → S}
  {a : ℕ ⇀ Ω → A}
  {r : ℕ ⇀ Ω → ℝ}
  {γ : ℝ}
  {t : ℕ}
  {Q : ℕ ⇀ S → A → ℝ}
  {V : ℕ ⇀ S → ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, Measurable (r[t], s[t], a[t]))
  (h₅ : ∀ t, V[t] s[t] =ᵐ[π] 𝔼[r: π]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s[t])) :
-- imply
  V[t] s[t] =ᵐ[π] 𝔼[s, a: π](Q[t] s[t] a[t] | s[t]) ∧
    Q[t] s[t] a[t] =ᵐ[π] 𝔼[r, s: π](r[t] + γ * V[t + 1] s[t + 1] | s[t], a[t]) := by
  sorry
`;

const codes = compile(src).render2vue(false);
const given = codes.lemma[0].given ?? [];
const imply = codes.lemma[0].imply;
const h5 = given.find((g) => (g.lean ?? '').includes('V[t] s[t]'));
const h5Latex = h5?.latex ?? '';
const implyLatex = imply?.latex ?? '';

check('found h₅', !!h5, given.map((g) => g.lean).join(' | '));
check(
  'h₅: value-position s[t] head is red',
  /V\[t\].*\\color\{red\}\s*\{s\}|{\\color\{red\} \{s\}}/.test(h5Latex) ||
    h5Latex.includes('{\\color{red} {s}}'),
  h5Latex.slice(0, 400),
);
check(
  'h₅: V is not painted red as an RV head',
  !/{\\color\{red\} \{V\}}/.test(h5Latex),
  h5Latex.slice(0, 400),
);
check(
  'imply: s/a/r heads red in value position',
  implyLatex.includes('{\\color{red} {s}}') && implyLatex.includes('{\\color{red} {a}}'),
  implyLatex.slice(0, 400),
);
check(
  'imply: Q and V not red',
  !/{\\color\{red\} \{Q\}}/.test(implyLatex) && !/{\\color\{red\} \{V\}}/.test(implyLatex),
  implyLatex.slice(0, 400),
);

import fs from 'fs';
const fullPath =
  'Lemma/Random/MEq_Expect/MEq_Expect/MEq_Expect/of/All_MEq_Expect/All_MEq_Expect/CondIndep_Joint/GtInftySup/All_MeasurableJoint/In_Ico.lean';
const full = fs.readFileSync(fullPath, 'utf8');
const fullCodes = compile(full).render2vue(false);
const fullH5 = (fullCodes.lemma[0].given ?? []).find((g) => (g.lean ?? '').includes('V[t] s[t] =ᵐ'));
const fullLatex = fullH5?.latex ?? '';
check(
  'In_Ico.lean h₅: s red in V[t] s[t]',
  fullLatex.includes('{\\color{red} {s}}'),
  fullLatex.slice(0, 400),
);
check(
  'In_Ico.lean h₅: V not red',
  !/{\\color\{red\} \{V\}}/.test(fullLatex),
  fullLatex.slice(0, 400),
);

if (failed) {
  console.error(`${failed} failure(s)`);
  process.exit(1);
}
console.log('all ok');
