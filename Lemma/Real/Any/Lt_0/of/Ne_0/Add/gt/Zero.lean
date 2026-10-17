import Lemma.Real.Any.Lt_0.of.Add.gt.Zero
import sympy.Basic
open Real


@[path]
private lemma main
  {a b c : ℝ}
-- given
  (h₀ : a ≠ 0)
  (h₁ : b ^ 2 - 4 * a * c > 0) :
-- imply
  ∃ x : ℝ, a * x ^ 2 + b * x + c < 0 := by
-- proof
  if ha : 0 < a then
    exact Any.Lt_0.of.Add.gt.Zero h₁
  else
    have : a < 0 := lt_of_le_of_ne (le_of_not_gt ha) h₀
    exact Any.Lt_0.of.Add.gt.Zero h₁


-- created on 2026-10-11
-- updated on 2026-10-17
