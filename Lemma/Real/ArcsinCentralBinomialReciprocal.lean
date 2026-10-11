import Mathlib
import sympy.Basic
import sympy.functions.special.ArcsinCentralBinomialReciprocal

/--
[ArcsinCentralBinomialReciprocal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ArcsinCentralBinomialReciprocal.lean)
-/
@[path]
private lemma arcsin_central_binomial_reciprocal_series_is
-- given
  (x : ℝ)
  (hx : |x| < 1) :
-- imply
  HasSum (fun m : ℕ =>
      (2 * x) ^ (2 * (m + 1)) / ((↑(m + 1) : ℝ) * ↑(Nat.choose (2 * (m + 1)) (m + 1))))
    ((2 * x / Real.sqrt (1 - x ^ 2)) * Real.arcsin x) := by
-- proof
  apply MetaMathlibExt.arcsin_central_binomial_reciprocal_series x hx

-- created on 2026-10-10
