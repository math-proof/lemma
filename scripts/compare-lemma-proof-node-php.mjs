/**
 * Fetch lemma HTML from the Node server and PHP `lean.php`, extract the embedded
 * `createApp('render', …)` payload, and compare `lemma[].proof`.
 *
 * By default only `proof.by[].lean` is compared (LaTeX ignored). For full step
 * equality including `latex`, set LEAN_PROOF_COMPARE_INCLUDE_LATEX=1.
 *
 * Usage:
 *   node scripts/compare-lemma-proof-node-php.mjs [module]
 *
 * Env (optional):
 *   LEAN_NODE_LEMMA_BASE  default http://127.0.0.1:3000/lean/
 *   LEAN_PHP_LEMMA_BASE   default http://127.0.0.1:8080/lean.php/
 *   LEAN_PROOF_COMPARE_INCLUDE_LATEX=1  compare latex too (legacy behavior)
 *
 * Exit: 0 same proof, 1 different, 2 fetch/parse error
 */
import process from 'process';
import {
  compareLemmaProof,
  lemmaProofCompareBases,
} from './lemmaProofNodePhpCore.mjs';

const moduleName =
  process.argv[2] || 'Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmax';

const bases = lemmaProofCompareBases();
const r = await compareLemmaProof(moduleName, bases);

console.log(`Module: ${r.moduleName}`);
console.log(`Node: ${r.nodeUrl}`);
console.log(`PHP:  ${r.phpUrl}`);

if (r.code === 0) {
  const mode =
    process.env.LEAN_PROOF_COMPARE_INCLUDE_LATEX === '1'
      ? 'lean + latex'
      : 'lean only';
  console.log(`Proof content: SAME (${mode}, all lemma[].proof match).`);
  process.exit(0);
}

if (r.code === 2) {
  console.error(r.message || 'error');
  process.exit(2);
}

console.error(r.message || 'Proof content: DIFFERENT.');
process.exit(1);
