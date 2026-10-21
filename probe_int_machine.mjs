import { compile } from './js/parser/lean.js';
import { readFileSync } from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';
const root = path.dirname(fileURLToPath(import.meta.url));
// when run from lean root, import works as js/parser/lean.js

const frag = `
lemma foo :
-- imply
  ∫ ω,
    ((γ ^ (id : ℕ → ℕ)) @ fun t ↦
      ((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => X (r · ω) (s · ω) (a · ω) (t + k))) •
        ∇[θ] Real.log (ℙ[M θ](a[t] = (a t ω) | s[t] = (s t ω))).toReal) ∂(M θ) =
    𝔼[r, s, a : M θ](
      (γ ^ (id : ℕ → ℕ)) @ fun t ↦
        (((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => X r s a (t + k))) •
          ∇[θ] Real.log (ℙ[M θ](a[t] | s[t])).toReal)) := by
  trivial
`;

const mod = compile(frag);
const latex = mod?.toLatex?.() ?? mod?.latex?.() ?? null;
// walk for imply
function walk(n, d=0) {
  if (!n || d>30) return;
  const name = n.constructor?.name;
  if (name === 'Lean_int' || name === 'LeanEq' || name === 'LeanArgsIndented' || name === 'LeanArgsNewLineSeparated' || name === 'Lean_partial') {
    let extra = '';
    if (name === 'Lean_int') {
      try { extra = ' measurePartial=' + !!n.measurePartial() + ' stack_scope=' + n.scope?.constructor?.name; } catch(e) {}
    }
    console.log('  '.repeat(d) + name + extra);
  }
  const kids = n.args || [];
  if (Array.isArray(kids)) for (const c of kids) walk(c, d+1);
  for (const k of ['lhs','rhs','scope','bound','arg','imply','proof']) {
    if (n[k] && typeof n[k]==='object') walk(n[k], d+1);
  }
}
console.log('module keys', mod && Object.keys(mod));
// try render2vue style
try {
  const { render2vueFromSource } = await import('./mjs/lean/compiler/index.mjs');
  const code = render2vueFromSource(frag, { user: 'lean' });
  const lat = code?.lemma?.[0]?.imply?.latex;
  console.log('IMPLY LATEX:');
  console.log(lat);
  console.log('bug trailing dω after =:', /=[\\s\\S]{0,300}mathrm\\{d\\}/.test(lat||''));
  console.log('has partial before =:', /partial[\\s\\S]{0,80}=/.test(lat||''));
} catch (e) {
  console.error('render fail', e);
}
