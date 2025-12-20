import Lemma.Set.Gt_Div1'3.of.In_Ico0.Sub.eq.DivSqrt3'2
import Lemma.Set.Lt_Div7'20.of.In_Ico0.Sub.eq.DivSqrt3'2
open Set


@[main]
private lemma main
  {x : ℝ}
-- given
  (h₀ : x ∈ Ico 0 (1 / 2))
  (h₁ : 3 * x - 4 * x³ = √3 / 2) :
-- imply
  x ∈ Ioo (1 / 3) (7 / 20) := by
-- proof
  have := Gt_Div1'3.of.In_Ico0.Sub.eq.DivSqrt3'2 h₀ h₁
  have := Lt_Div7'20.of.In_Ico0.Sub.eq.DivSqrt3'2 h₀ h₁
  constructor <;> assumption


-- created on 2025-03-24
