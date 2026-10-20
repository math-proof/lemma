import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ArithmeticFunction.WintnerMeanValue
open scoped BigOperators
open MetaMathlibExt


/--
[wintner_mean_value](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/WintnerMeanValue.lean)
-/
@[path]
private lemma wintner_mean_value_eq
  {f : ArithmeticFunction ℂ}
-- given
  (hsum : Summable (fun n : ℕ => ‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n‖ / (n : ℝ))) :
-- imply
  Filter.Tendsto (fun x : ℕ => ((x : ℂ)⁻¹) * ∑ n ∈ Finset.Icc 1 x, f n) Filter.atTop
    (nhds (∑' n : ℕ, ((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n /
    (n : ℂ))) := by
-- proof
  apply MetaMathlibExt.wintner_mean_value f hsum


-- created on 2026-10-20
