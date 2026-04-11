/**
 * Ports `php/lemma.php` lines 608–659: after `compile` + `render2vue`, `$syntax` keys drive extra
 * `stdlib.*` / `sympy.*` imports (`import_syntax`). Uses the same JS parser as `render2vue.mjs`.
 */
import { compile, LeanModule } from '../../static/js/parser/lean.js';

/**
 * @param {string[]} imports dotted import paths (no `import ` prefix), e.g. `stdlib.SEq`
 * @param {string} leanSource full `.lean` file text (imports + body)
 * @returns {string[]} `imports` plus any syntax-driven additions (PHP `array_unshift` order preserved in front segment)
 */
export function mergeSyntaxDrivenImports(imports, leanSource) {
  const out = imports.map(String);
  const has = (x) => out.includes(x);
  const unshiftIf = (imp) => {
    if (!has(imp)) out.unshift(imp);
  };

  let tree;
  try {
    tree = compile(leanSource);
  } catch {
    return out;
  }
  if (!(tree instanceof LeanModule) || typeof tree.render2vue !== 'function') {
    return out;
  }

  const modify = { value: false };
  /** @type {Record<string, boolean>} */
  const syntax = {};
  try {
    tree.render2vue(false, modify, syntax);
  } catch {
    return out;
  }

  for (const tac of Object.keys(syntax)) {
    switch (tac) {
      case 'denote':
        unshiftIf('sympy.core.relational');
        break;
      case 'mp':
      case 'mpr':
        unshiftIf('sympy.core.logic');
        break;
      case '²':
      case '³':
      case '⁴':
        unshiftIf('sympy.core.power');
        break;
      case 'Ici':
      case 'Iic':
      case 'Ioi':
      case 'Iio':
      case 'Ioc':
      case 'Ioo':
      case 'Icc':
      case 'Ico':
      case 'range':
        unshiftIf('sympy.sets.sets');
        break;
      case 'setOf':
        unshiftIf('sympy.concrete.quantifier');
        break;
      case 'LeanStack':
        unshiftIf('sympy.tensor.stack');
        break;
      case 'Tensor':
        if (!has('sympy.tensor.tensor') && !has('sympy.tensor.stack')) {
          unshiftIf('sympy.tensor.Basic');
        }
        break;
      case 'IntegerRing':
        unshiftIf('sympy.polys.domains');
        break;
      case 'KroneckerDelta':
        unshiftIf('sympy.functions.special.tensor_functions');
        break;
      case 'eye':
        unshiftIf('sympy.matrices.expressions.special');
        break;
      case '≃':
        unshiftIf('stdlib.SEq');
        break;
      case 'softmax':
        unshiftIf('sympy.tensor.functions');
        break;
      default:
        break;
    }
  }

  return out;
}
