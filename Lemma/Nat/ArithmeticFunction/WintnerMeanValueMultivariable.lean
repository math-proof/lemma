import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ArithmeticFunction.WintnerMeanValueMultivariable
open scoped BigOperators Topology
open MetaMathlibExt


/--
[wintner_mean_value_multivariable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/WintnerMeanValueMultivariable.lean)
-/
@[path]
private lemma wintner_mean_value_multivariable_eq
  {k : ℕ}
  {f : (Fin k → ℕ) → ℂ}
-- given
  (hk : 0 < k) :
-- imply
  let mobiusConvolution : (Fin k → ℕ) → ℂ := by
-- proof
  apply MetaMathlibExt.wintner_mean_value_multivariable k hk f


-- created on 2026-10-20
