import sympy.core.power
import sympy.polys.polyroots
import Lemma.Complex.OrEqS_Div_Mul2.of.Eq0AddAddMul_Square.Ne_0
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
  have h : a * x² + 0 * x + c = 0 := by
    simpa using h₁
  simpa using OrEqS_Div_Mul2.of.Eq0AddAddMul_Square.Ne_0 h₀ h


-- created on 2018-08-15
-- updated on 2026-08-20
