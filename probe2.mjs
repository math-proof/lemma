import { readFileSync } from 'fs';
import { render2vueFromSource } from './mjs/lean/compiler/index.mjs';

const path = 'Lemma/Random/Integral_Ext_FunPowDot/eq/ExpectFunPowDot/of/GtInftySup/All_Differentiable_Prob/All_NeProb_0/All_LeNormFunPowDot/All_MeasurableFun/IsPolicyTrajectory/In_Ico0.lean';
const src = readFileSync(path, 'utf8');
const code = render2vueFromSource(src, { user: 'lean' });
const lat = code?.lemma?.[0]?.imply?.latex ?? '';
console.log(lat);
console.log('---');
console.log('ends with dω:', /mathrm\{d\}\}\{ω\}\s*$/.test(lat));
console.log('has \\partial before first =:', lat.indexOf('partial') >= 0 && (lat.indexOf('partial') < lat.indexOf('=')));
console.log('format like int ω, f partial:', /\\int \{[^}]*ω/.test(lat) || /\\int \{%s\}/.test(lat));
console.log('int opener:', lat.slice(0, 80));
console.log('around partial/= :');
const i = lat.indexOf('partial');
console.log(lat.slice(Math.max(0,i-40), i+120));
console.log('tail:', lat.slice(-120));
