import Lemma.Set.Gt_Div1'3.of.In_Ico0.Sub.eq.DivSqrt3'2
import Lemma.Set.Lt_Div7'20.of.In_Ico0.Sub.eq.DivSqrt3'2
open Set


/--
Given a real number `x` in the interval `[0, 1/2)` that satisfies the equation `3x - 4x^3 = √3 / 2`, this lemma establishes that `x` must lie strictly between `1/3` and `7/20`.
The proof leverages previously established bounds to combine the inequalities `x > 1/3` and `x < 7/20`, thereby confining `x` to the open interval `(1/3, 7/20)`.
-/
@[main]
private lemma main
  {x : ℝ}
-- given
  (h₀ : x ∈ Ico 0 (1 / 2))
  (h₁ : 3 * x - 4 * x ^ 3 = √3 / 2) :
-- imply
  x ∈ Ioo (1 / 3) (7 / 20) := by
-- proof
  have := Gt_Div1'3.of.In_Ico0.Sub.eq.DivSqrt3'2 h₀ h₁
  have := Lt_Div7'20.of.In_Ico0.Sub.eq.DivSqrt3'2 h₀ h₁
  constructor <;> assumption


-- created on 2025-03-24
