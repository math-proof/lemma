import MarkdownParser from './js/parser/markdown.js';

const comment = `| attributes | lemma |
| :---: | :---: |
| path | Random.ExpectFunPowDot.eq.Integral_Ext_FunPowDot.of.GtInftySup.All_Differentiable_Prob.All_NeProb_0.AeGtInftySup.All_MeasurableFun.IsPolicyTrajectory.In_Ico0 |
| comm | Random.Integral_Ext_FunPowDot.eq.ExpectFunPowDot.of.GtInftySup.All_Differentiable_Prob.All_NeProb_0.AeGtInftySup.All_MeasurableFun.IsPolicyTrajectory.In_Ico0 |
`;

const md = new MarkdownParser();
md.build(comment);
console.log('html:', md.html);
console.log('str:', String(md));
console.log('root ctor:', md.root?.constructor?.name);
console.log('root.args len:', md.root?.args?.length);
for (const a of md.root?.args || []) {
  console.log(' arg', a.constructor?.name, 'func=', a.func, 'args=', a.args?.length);
  if (a.args) {
    for (const b of a.args) {
      console.log('  ', b.constructor?.name, 'func=', b.func, 'text=', b.text ?? '', 'args=', b.args?.length);
      if (b.args) for (const c of b.args) {
        console.log('    ', c.constructor?.name, 'func=', c.func, 'text=', JSON.stringify(String(c.text??c).slice(0,80)));
      }
    }
  }
}
const bind = md.root.bind;
console.log('bind keys', Object.keys(bind||{}));
console.log('bind.args len', bind?.args?.length);
console.log('components has MarkdownTABLE?', !!MarkdownParser.components?.MarkdownTABLE);
console.log('component keys sample', Object.keys(MarkdownParser.components||{}).filter(k=>k.includes('TABLE')||k.includes('TR')||k.includes('TD')||k.includes('TH')));
