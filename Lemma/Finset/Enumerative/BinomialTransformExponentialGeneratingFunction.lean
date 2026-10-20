import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.BinomialTransformExponentialGeneratingFunction
open MetaMathlibExt


/--
[exponentialGeneratingFunction_binomialTransform](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTransformExponentialGeneratingFunction.lean)
-/
@[path]
private lemma exponentialGeneratingFunction_binomialTransform_eq
  {a b : ℕ → ℝ}
  {A : ℝ → ℝ}
-- given
  (hbinomial : ∀ n : ℕ, b n = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * a k) :
-- imply
  ∀ t : ℝ, HasSum (fun n : ℕ => a n * t ^ n / n.factorial) (A t) →
    HasSum (fun n : ℕ => b n * t ^ n / n.factorial)
    (Real.exp t * A t) := by
-- proof
  apply MetaMathlibExt.exponentialGeneratingFunction_binomialTransform a b A hbinomial


-- created on 2026-10-20
