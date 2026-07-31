import Lemma.Rat.EqMul.is.Eq_Div.of.Ne_0
import Lemma.Complex.EqSquareSqrt
import Lemma.Real.OrEqS.of.Square
import Lemma.Rat.SquareDiv.eq.DivSquareS
import Lemma.Rat.DivNeg.eq.NegDiv
open Complex Rat Real


@[main]
private lemma main
  {x a c : ℂ}
-- given
  (h₀ : a ≠ 0)
  (h₁ : a * x² = c) :
-- imply
  x = √(a * c) / a ∨
    x = -√(a * c) / a := by
-- proof
  have hx₂ : x² = c / a := Eq_Div.of.EqMul.Ne_0.left h₀ h₁
  have ht₂ : (√(a * c) / a)² = c / a := by
    rw [SquareDiv.eq.DivSquareS]
    rw [EqSquareSqrt]
    field_simp [h₀]
  obtain h | h := OrEqS.of.Square (hx₂.trans ht₂.symm)
  · exact Or.inl h
  · apply Or.inr
    rwa [DivNeg.eq.NegDiv]


-- created on 2024-07-01
