import Lemma.Complex.OrEqS_Div.of.Eq0Add_Mul_Square.Ne_0
open Complex


@[main]
private lemma main
  {x a c : ℂ}
-- given
  (h₀ : a ≠ 0)
  (h₁ : a * x² + c = 0) :
-- imply
  x = √(-4 * a * c) / (2 * a) ∨ x = -√(-4 * a * c) / (2 * a) := by
-- proof
  have h : c + 0 * x + a * x² = 0 := by
    rw [(by ring : c + 0 * x + a * x² = a * x² + c)]
    apply h₁
  simpa using OrEqS_Div.of.Eq0Add_Mul_Square.Ne_0 h₀ h


-- created on 2018-08-15
-- updated on 2026-08-22
