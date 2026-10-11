import Mathlib
import sympy.Basic
import sympy.series.RisingProductSeries


/--
[RisingProductSeries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecificLimits/RisingProductSeries.lean)
-/
@[path]
private lemma summable_neg_pow_mul_pow_div_prod_add_mul_is
-- given
  (b c : ℂ)
  (hc : ∀ r : ℕ, c + b * ((r + 1 : ℕ) : ℂ) ≠ 0)
  (x : ℂ) :
-- imply
  Summable (fun j : ℕ =>
    (-b) ^ j * x ^ (j + 1) / ∏ r ∈ Finset.range (j + 1), (c + b * ((r + 1 : ℕ) : ℂ))) := by
-- proof
  apply Complex.summable_neg_pow_mul_pow_div_prod_add_mul x hc


-- created on 2026-10-11
