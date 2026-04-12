/**
 * Ports `php/lemma.php` lines 608–659: after `compile` + `render2vue`, `$syntax` keys drive extra
 * `stdlib.*` / `sympy.*` imports (`import_syntax`). Uses the same JS parser as `render2vue.mjs`.
 *
 * Skips adding an import when PHP would: already present, or implied by `Lemma.*` via MySQL
 * recursive deps (`importSyntaxDeps.mjs`) or filesystem `contains_module`.
 */
import { compile, LeanModule } from '../../static/js/parser/lean.js';
import { transitiveProvidesImport } from './importSyntaxDeps.mjs';

/**
 * @param {string[]} imports dotted import paths (no `import ` prefix), e.g. `stdlib.SEq`
 * @param {string} leanSource full `.lean` file text (imports + body)
 * @returns {Promise<string[]>} `imports` plus any syntax-driven additions (PHP `array_unshift` order)
 */
export async function mergeSyntaxDrivenImports(imports, leanSource) {
  const out = imports.map(String);
  const has = (x) => out.includes(x);

  /**
   * @param {string} imp
   */
  const maybeUnshift = async (imp) => {
    if (has(imp)) return;
    if (await transitiveProvidesImport(out, imp)) return;
    out.unshift(imp);
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
        await maybeUnshift('sympy.core.relational');
        break;
      case 'mp':
      case 'mpr':
        await maybeUnshift('sympy.core.logic');
        break;
      case '²':
      case '³':
      case '⁴':
        await maybeUnshift('sympy.core.power');
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
        await maybeUnshift('sympy.sets.sets');
        break;
      case 'setOf':
        await maybeUnshift('sympy.concrete.quantifier');
        break;
      case 'LeanStack':
        await maybeUnshift('sympy.tensor.stack');
        break;
      case 'Tensor':
        if (!has('sympy.tensor.tensor') && !has('sympy.tensor.stack')) {
          await maybeUnshift('sympy.tensor.Basic');
        }
        break;
      case 'IntegerRing':
        await maybeUnshift('sympy.polys.domains');
        break;
      case 'KroneckerDelta':
        await maybeUnshift('sympy.functions.special.tensor_functions');
        break;
      case 'eye':
        await maybeUnshift('sympy.matrices.expressions.special');
        break;
      case '≃':
        await maybeUnshift('stdlib.SEq');
        break;
      case 'softmax':
        await maybeUnshift('sympy.tensor.functions');
        break;
      default:
        break;
    }
  }

  return out;
}
