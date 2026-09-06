import Lemma.Real.Ge0SubSquare_MulMul4.of.All_Le0Add_Mul_Square.Ge_0
open Real


@[main]
private lemma main
  {a b c : ℝ}
-- given
  (h₀ : a ≥ 0)
  (h₁ : ∀ x : ℝ, c + b * x + a * x² ≥ 0) :
-- imply
  b² ≤ 4 * a * c := by
-- proof
  have := Ge0SubSquare_MulMul4.of.All_Le0Add_Mul_Square.Ge_0 h₀ h₁
  simp_all


-- created on 2025-04-06
-- updated on 2026-09-06
