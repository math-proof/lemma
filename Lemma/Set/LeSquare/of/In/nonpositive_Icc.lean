import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x m : ℝ}
-- given
  (h : x ∈ Set.Icc m 0) :
-- imply
  x * x ≤ m * m := by
-- proof
  have h₁ : (0:ℝ) ≤ -x := neg_nonneg.mpr h.2
  have h₂ : -x ≤ -m := neg_le_neg h.1
  have := mul_self_le_mul_self h₁ h₂
  rwa [neg_mul_neg, neg_mul_neg] at this


-- created on 2021-03-11
