import sympy.core.power
import sympy.polys.polyroots
import Lemma.Complex.Imp_Eq_0.Imp_Eq_DivNeg.Imp_OrEqS_Div_Mul2.of.Eq0AddAddMul_Square
open Complex


@[main]
private lemma main
  {x a b c : ℂ}
-- given
  (h : a * x² + b * x + c = 0) :
-- imply
  ((a = 0 ∧ b = 0) → c = 0) ∧
    ((a = 0 ∧ b ≠ 0) → x = -c / b) ∧
    (a ≠ 0 →
      let Δ : ℂ := b² - 4 * a * c
      x = (-b + √Δ) / (2 * a) ∨ x = (-b - √Δ) / (2 * a)) :=
-- proof
  Imp_Eq_0.Imp_Eq_DivNeg.Imp_OrEqS_Div_Mul2.of.Eq0AddAddMul_Square h


-- created on 2018-08-17
-- updated on 2026-08-20
