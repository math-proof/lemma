import sympy.core.power
import sympy.polys.polyroots
import Lemma.Complex.OrEqS_Div.of.Eq0AddAddMul_Square.of.Ne_0
import Lemma.Complex.Or_Eq_NegSqrt.of.EqSquare
open Complex


@[main]
private lemma main
  {x α γ : ℂ}
-- given
  (h : x ^ 4 + α * x ^ 2 + γ = 0) :
-- imply
  let Δ : ℂ := α ^ 2 - 4 * γ
  x = √(√Δ / 2 - α / 2) ∨
    x = -√(√Δ / 2 - α / 2) ∨
    x = √(-√Δ / 2 - α / 2) ∨
    x = -√(-√Δ / 2 - α / 2) := by
-- proof
  intro Δ
  have hy : (1 : ℂ) * (x ^ 2) ^ 2 + α * x ^ 2 + γ = 0 := by
    convert h
    ring
  have hquad := OrEqS_Div.of.Eq0AddAddMul_Square.of.Ne_0 hy
  have hone : (1 : ℂ) ≠ 0 := one_ne_zero
  obtain ⟨_, _, hroot⟩ := hquad
  have hΔ : (α ^ 2 - 4 * (1 : ℂ) * γ) = Δ := by
    simp [Δ]
  obtain hpos | hneg := hroot hone
  ·
    rw [hΔ] at hpos
    have hx2 : x ^ 2 = √Δ / 2 - α / 2 := by
      convert hpos using 1
      ring
    have := Or_Eq_NegSqrt.of.EqSquare hx2
    rcases this with hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inl hx)
  ·
    rw [hΔ] at hneg
    have hx2 : x ^ 2 = -√Δ / 2 - α / 2 := by
      convert hneg using 1
      ring
    have := Or_Eq_NegSqrt.of.EqSquare hx2
    rcases this with hx | hx
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inr (Or.inr hx))


-- created on 2018-11-26
-- updated on 2026-08-20
