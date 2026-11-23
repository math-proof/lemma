/**
 * `paren-getelem`: skip notation-body parentheses of ℙ / 𝔼 / 𝕍𝕒𝕣 / ℂ𝕠𝕧, which
 * are part of the macro syntax and cannot be removed (`𝔼[x[k]: π](x[k])`).
 * Genuine redundant `(x[k])` still warns.
 * Run: node mjs/lean/lint/astRules.parenGetElem.test.mjs
 */
import { lintLean } from './index.mjs';

let failed = 0;
function check(name, cond, detail = '') {
  if (cond) console.log('PASS', name);
  else {
    failed++;
    console.error('FAIL', name, detail);
  }
}

const OPT = { file: 'Lemma/Foo.lean', rules: ['paren-getelem'], today: '2026-11-22' };

const src = (body) => `lemma foo : True := by\n  have h := ${body}\n  trivial\n`;

function getelem(source) {
  return lintLean(source, OPT).filter((w) => w.rule === 'paren-getelem');
}

const SIG = `private lemma main
  {x : ℕ → Ω → ℝ} {π : Measure Ω} {μ : ℝ}
-- given
  (h₃ : ∀ k : ℕ, 𝔼[x[k]: π](x[k]) = μ)
  (h₄ : ∀ k : ℕ, 𝕍𝕒𝕣[x[k]: π](x[k]) = σ²) :
-- imply
  True := by
  sorry
`;

{
  const ws = getelem(SIG);
  check(
    'no warning on 𝔼[x[k]: π](x[k]) / 𝕍𝕒𝕣[x[k]: π](x[k]) signature bodies',
    ws.length === 0,
    JSON.stringify(ws.map((w) => ({ line: w.line, info: w.info, stmt: w.stmt }))),
  );
}

{
  const ws = getelem(src('ℙ[π](x[k])'));
  check('no warning on ℙ[π](x[k]) body', ws.length === 0, JSON.stringify(ws.map((w) => w.info)));
}

{
  const ws = getelem(src('ℂ𝕠𝕧[x[k], y: π](x[k])'));
  check('no warning on ℂ𝕠𝕧[x[k], y: π](x[k]) body', ws.length === 0, JSON.stringify(ws.map((w) => w.info)));
}

{
  const ws = getelem(src('Nat.succ (x[k])'));
  check(
    'still flags Nat.succ (x[k])',
    ws.some((w) => w.rule === 'paren-getelem' && (w.info.includes('(x[k])') || (w.stmt || '').includes('(x[k])'))),
    JSON.stringify(ws.map((w) => w.info)),
  );
}

{
  const ws = getelem(src('(x[k]) + 1'));
  check(
    'still flags (x[k]) + 1',
    ws.some((w) => w.rule === 'paren-getelem'),
    JSON.stringify(ws.map((w) => w.info)),
  );
}

{
  const ws = getelem(src('((x[k]))'));
  check(
    'still flags inner pair of ((x[k]))',
    ws.some((w) => w.rule === 'paren-getelem'),
    JSON.stringify(ws.map((w) => w.info)),
  );
}

{
  const ws = getelem(src('𝔼[x[k]: π]((x[k]) + 1)'));
  check(
    'still flags inner (x[k]) inside 𝔼 body, not the notation delimiters',
    ws.length === 1 && ws[0].rule === 'paren-getelem' && (ws[0].stmt || '').trim() === '(x[k])',
    JSON.stringify(ws.map((w) => ({ info: w.info, stmt: w.stmt }))),
  );
}

{
  // Notation bodies plus a genuine later hit must still produce a warning.
  const mixed = `private lemma main
  {x : ℕ → Ω → ℝ} {π : Measure Ω} {μ : ℝ}
-- given
  (h₃ : ∀ k : ℕ, 𝔼[x[k]: π](x[k]) = μ) :
-- imply
  True := by
  have h := Nat.succ (x[k])
  trivial
`;
  const ws = getelem(mixed);
  check(
    'mixed: notation body silent, later Nat.succ (x[k]) still warns',
    ws.length === 1 && ws[0].rule === 'paren-getelem',
    JSON.stringify(ws.map((w) => ({ line: w.line, info: w.info, stmt: w.stmt }))),
  );
}

console.log(failed ? `\n${failed} FAILED` : '\nall passed');
process.exit(failed ? 1 : 0);
