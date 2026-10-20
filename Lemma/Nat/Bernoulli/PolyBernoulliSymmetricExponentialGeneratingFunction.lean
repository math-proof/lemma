import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Bernoulli.PolyBernoulliSymmetricExponentialGeneratingFunction
open scoped BigOperators
open MetaMathlibExt


/--
[polyBernoulli_negative_symmetric_exponential_generating_function](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/PolyBernoulliSymmetricExponentialGeneratingFunction.lean)
-/
@[path]
private lemma polyBernoulli_negative_symmetric_exponential_generating_function_eq
  {B : ℕ → ℕ → ℝ}
  {x y : ℝ}
-- given
  (hB : ∀ n k : ℕ, B n k = ∑ j ∈ Finset.range (min n k + 1), (j.factorial : ℝ) ^ 2 * Nat.stirlingSecond (n + 1) (j + 1) * Nat.stirlingSecond (k + 1) (j + 1))
  (hxy : (Real.exp |x| - 1) * (Real.exp |y| - 1) < 1) :
-- imply
  (∑' n : ℕ, ∑' k : ℕ,
    B n k * (x ^ n / n.factorial) * (y ^ k / k.factorial)) =
    Real.exp (x + y) /
    (Real.exp x + Real.exp y - Real.exp (x + y)) := by
-- proof
  apply MetaMathlibExt.polyBernoulli_negative_symmetric_exponential_generating_function B hB x y hxy


-- created on 2026-10-20
