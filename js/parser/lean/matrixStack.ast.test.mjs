/**
 * Matrix `[i < n, j < n] body` → LeanStack (comma of two Lean_lt);
 * Tensor `[i < n]` / nested `[i < n] [j < n]` stay LeanStack as before.
 * Run: `node js/parser/lean/matrixStack.ast.test.mjs`
 */
import { compile } from '../lean.js';
import { Lean } from './base.js';
import fs from 'fs';

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

function findStacks(n, out = []) {
  if (!n || typeof n !== 'object') return out;
  if (n instanceof L.LeanStack) out.push(n);
  if (Array.isArray(n.args)) for (const a of n.args) findStacks(a, out);
  return out;
}

function findBrackets(n, out = []) {
  if (!n || typeof n !== 'object') return out;
  if (n instanceof L.LeanBracket) out.push(n);
  if (Array.isArray(n.args)) for (const a of n.args) findBrackets(a, out);
  return out;
}

{
  const tree = compile(`
lemma main {n : ℕ} {f : Fin n → Fin n → ℝ} :
  ([i < n, j < n] f i j).det = 0 := by
  sorry
`);
  const stacks = findStacks(tree);
  const brackets = findBrackets(tree).filter((b) => String(b).includes('i < n'));
  check('matrix comma → LeanStack', stacks.length >= 1, `stacks=${stacks.length}`);
  check('no leftover i<n bracket', brackets.length === 0, brackets.map((b) => String(b)).join(' | '));
  const st = stacks.find((s) => s.matrixFinBinders());
  check('matrixFinBinders()', !!st, stacks.map((s) => String(s.bound)).join(' | '));
  const [a, b] = st?.matrixFinBinders() ?? [];
  check('two lt binders i,j', a?.lhs?.text === 'i' && b?.lhs?.text === 'j', `${a?.lhs?.text},${b?.lhs?.text}`);
  check('scope is f i j app', /f/.test(String(st?.scope ?? '')), String(st?.scope));
  check('reprint keeps comma sugar', /\[i < n, j < n\]/.test(String(st)), String(st));
}

{
  const tree = compile(`
lemma main {n : ℕ} {f : Fin n → ℝ} :
  [i < n] f i = 0 := by
  sorry
`);
  const stacks = findStacks(tree);
  check('tensor single → LeanStack', stacks.length === 1);
  check('tensor not matrixFinBinders', stacks[0] && !stacks[0].matrixFinBinders());
  check('tensor bound is Lean_lt', stacks[0]?.bound instanceof L.Lean_lt);
}

{
  const tree = compile(`
lemma main {n : ℕ} {f : Fin n → Fin n → ℝ} :
  [i < n] [j < n] f i j = 0 := by
  sorry
`);
  const stacks = findStacks(tree);
  check('tensor nested → two LeanStacks', stacks.length === 2, `got ${stacks.length}`);
  check('neither is matrix comma', stacks.every((s) => !s.matrixFinBinders()));
  check('outer scope is inner Stack', stacks.some((s) => s.scope instanceof L.LeanStack));
}

{
  // Indented Matrix sugar (repro): must NOT be
  //   Parenthesis(ArgsIndented(Bracket(Comma(lt,lt)), NewLineSeparated(Mul…)))
  // but
  //   Property(Parenthesis(Stack(Comma(lt,lt), NewLineSeparated(Mul…))), Tok(det))
  const f = 'Lemma/Matrix/DetOfFunMul_Sum_Mul_Pow_Sub/eq/PowSub__Mul.lean';
  const tree = compile(fs.readFileSync(f, 'utf8'));
  const st = findStacks(tree).find((s) => s.matrixFinBinders());
  check('PowSub__Mul lemma has matrix LeanStack', !!st, findStacks(tree).map((s) => String(s).slice(0, 60)).join(' || '));
  check('lemma body under stack has choose/sum', /choose|∑/.test(String(st?.scope ?? '')), String(st?.scope).slice(0, 80));
  check('indented scope is NewLineSeparated under Stack', st?.scope instanceof L.LeanArgsNewLineSeparated);
  check('Stack.args = [Comma, scope]', st?.args?.length === 2 && st.args[0] === st.bound && st.args[1] === st.scope);
  let eq = null;
  (function walk(n) {
    if (!n || typeof n !== 'object') return;
    if (n instanceof L.LeanEq && !eq) eq = n;
    if (Array.isArray(n.args)) for (const a of n.args) walk(a);
  })(tree);
  const lhs = eq?.args?.[0];
  check('LHS is .det Property', lhs instanceof L.LeanProperty && lhs.args?.[1]?.text === 'det');
  const paren = lhs?.args?.[0];
  check('det of Parenthesis(Stack)', paren instanceof L.LeanParenthesis && paren.arg === st);
  const badBracket = findBrackets(tree).some((b) => {
    const a = b.arg;
    if (!(a instanceof L.LeanArgsCommaSeparated)) return false;
    const parts = a.args.filter((x) => !(x instanceof L.LeanCaret));
    return parts.length === 2 && parts.every((p) => p instanceof L.Lean_lt);
  });
  check('no Bracket(Comma(lt,lt)) leftover', !badBracket);
}

if (failed) {
  console.error(`${failed} failure(s)`);
  process.exit(1);
}
console.log('all ok');
