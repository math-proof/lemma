import Mathlib
import sympy.Basic
import sympy.matrices.inner_product_space.DiscreteSpectrum
open scoped BigOperators


/--
[DiscreteSpectrum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/DiscreteSpectrum.lean)
-/
@[path]
private lemma riesz_mean_zero_eq
-- given
  (S : NonnegativeDiscreteSpectrum)
  (Λ : ℝ) :
-- imply
  S.rieszMean 0 Λ = S.countingFunction Λ := by
-- proof
  apply NonnegativeDiscreteSpectrum.rieszMean_zero S Λ

-- created on 2026-10-10
-- updated on 2026-10-23
