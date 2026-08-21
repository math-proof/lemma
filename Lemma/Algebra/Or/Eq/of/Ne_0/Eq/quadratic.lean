import sympy.core.power
import sympy.polys.polyroots
import Lemma.Complex.OrEqS_Div_Mul2.of.Eq0AddAddMul_Square.Ne_0
open Complex


@[main]
private lemma main
  {x a b c : ℂ}
-- given
  (h₀ : a ≠ 0)
  (h₁ : a * x² + b * x + c = 0) :
-- imply
  let Δ : ℂ := b² - 4 * a * c
  x = (-b + √Δ) / (2 * a) ∨ x = (-b - √Δ) / (2 * a) :=
-- proof
  OrEqS_Div_Mul2.of.Eq0AddAddMul_Square.Ne_0 h₀ h₁


-- created on 2018-08-15
-- updated on 2026-08-20
