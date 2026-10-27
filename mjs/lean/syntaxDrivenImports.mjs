/**
 * Ports `php/lemma.php` lines 608–659: after `compile` + `render2vue`, `$syntax` keys drive extra
 * decl-library imports (`import_syntax`). Uses the same JS parser as `render2vue.mjs`.
 *
 * Skips adding an import when PHP would: already present, or implied by `Lemma.*` via MySQL
 * recursive deps (`importSyntaxDeps.mjs`) or filesystem `contains_module`.
 */
import { compile, LeanModule } from '../../js/parser/lean.js';
import { transitiveProvidesImport } from './importSyntaxDeps.mjs';

/**
 * @param {string[]} imports dotted import paths (no `import ` prefix), e.g. `Theorem.Logic.SEq`
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
        await maybeUnshift('Def.Tactic.Logic.Part4');
        break;
      case 'mp':
      case 'mpr':
        await maybeUnshift('Def.Tactic.Logic.Part4');
        break;
      case '²':
      case '³':
      case '⁴':
        await maybeUnshift('Theorem.Algebra.Power.Part2');
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
        await maybeUnshift('Theorem.Data.Set.Sets');
        break;
      case 'setOf':
        await maybeUnshift('Macro.Logic.Quantifier.Part4');
        break;
      case 'LeanStack':
        await maybeUnshift('Def.Data.Holor.Stack.Part2');
        break;
      case 'Tensor':
        if (!has('Instance.Data.Holor.Tensor.Part2') && !has('Def.Data.Holor.Stack.Part2')) {
          await maybeUnshift('Def.Data.Holor.Defs.Part4');
        }
        break;
      case 'IntegerRing':
        await maybeUnshift('Instance.Data.Int.Integers');
        break;
      case 'KroneckerDelta':
        await maybeUnshift('Def.Analysis.SpecialFunctions.TensorFunctions');
        break;
      case 'eye':
        await maybeUnshift('Def.Data.Holor.BandPart');
        break;
      case '≃':
        await maybeUnshift('Theorem.Logic.SEq');
        break;
      case '≈':
        await maybeUnshift('Theorem.Analysis.Real.Relational');
        break;
      case 'softmax':
        await maybeUnshift('Def.Data.Holor.Softmax');
        break;
      case 'sigmoid':
        await maybeUnshift('Instance.Data.Vector.Functions.Part2');
        break;
      default:
        break;
    }
  }

  return out;
}
