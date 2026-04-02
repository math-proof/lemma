/**
 * Fetch Node + PHP lemma HTML for hard-coded sample modules and print the first
 * proof-step mismatch (lean + latex) for each.
 *
 *   node scripts/inspect-lemma-proof-diff-sample.mjs
 */
import {
  extractPayload,
  lemmaProofCompareBases,
  lemmaUrl,
  deepEqualProofPayload,
} from './lemmaProofNodePhpCore.mjs';

async function fetchText(url) {
  const res = await fetch(url, { redirect: 'follow' });
  if (!res.ok) throw new Error(`${res.status} ${res.statusText}`);
  return res.text();
}

const SAMPLES = [
  'Bool.All_And.of.All.All',
  'Bool.All_Any_All_And.of.All_Any.All',
  'Bool.All_Any_Eq_Cast.of.Eq',
  'Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmax',
  'Bool.All_Eq.of.All_Eq.Surjective',
];

const bases = lemmaProofCompareBases();

for (const mod of SAMPLES) {
  console.log('\n========', mod, '========');
  const nu = lemmaUrl(bases.nodeBase, mod);
  const pu = lemmaUrl(bases.phpBase, mod);
  let nodePayload;
  let phpPayload;
  try {
    const [nh, ph] = await Promise.all([fetchText(nu), fetchText(pu)]);
    nodePayload = extractPayload(nh);
    phpPayload = extractPayload(ph);
  } catch (e) {
    console.log('fetch error:', String(e.message || e));
    continue;
  }

  const nLem = nodePayload.lemma;
  const pLem = phpPayload.lemma;
  if (!Array.isArray(nLem) || !Array.isArray(pLem)) {
    console.log('missing lemma array');
    continue;
  }
  console.log('lemma[] count node:', nLem.length, 'php:', pLem.length);

  for (let li = 0; li < Math.min(nLem.length, pLem.length); li++) {
    const np = nLem[li]?.proof;
    const pp = pLem[li]?.proof;
    if (!deepEqualProofPayload(np, pp)) {
      console.log(`first mismatch: lemma[${li}] name=${JSON.stringify(nLem[li]?.name)}`);
      const nb = np?.by;
      const pb = pp?.by;
      if (!Array.isArray(nb) || !Array.isArray(pb)) {
        console.log('proof.by not arrays', typeof nb, typeof pb);
        break;
      }
      console.log('proof.by length node:', nb.length, 'php:', pb.length);
      for (let si = 0; si < Math.max(nb.length, pb.length); si++) {
        if (!deepEqualProofPayload(nb[si], pb[si])) {
          console.log(`  step proof.by[${si}]:`);
          console.log('  NODE lean:', JSON.stringify(nb[si]?.lean));
          console.log('  PHP  lean:', JSON.stringify(pb[si]?.lean));
          console.log('  lean same?', nb[si]?.lean === pb[si]?.lean);
          const nl = nb[si]?.latex;
          const pl = pb[si]?.latex;
          console.log('  NODE latex (first 200):', String(nl).slice(0, 200));
          console.log('  PHP  latex (first 200):', String(pl).slice(0, 200));
          console.log('  latex same?', JSON.stringify(nl) === JSON.stringify(pl));
          break;
        }
      }
      break;
    }
  }
}
