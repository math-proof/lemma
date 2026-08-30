import Lemma.Complex.OrEqS_Div.of.Eq0Add_Mul_Square.Ne_0
import Lemma.Complex.Or_Eq_NegSqrt.of.EqSquare
open Complex


@[main]
private lemma biquadratic
  {x α γ : ℂ}
-- given
  (h : γ + α * x ^ 2 + x ^ 4 = 0) :
-- imply
  let Δ := α ^ 2 - 4 * γ
  (x = √((√Δ - α) / 2) ∨ x = -√((√Δ - α) / 2)) ∨
    x = √((-√Δ - α) / 2) ∨
    x = -√((-√Δ - α) / 2) := by
-- proof
  intro Δ
  have hy : γ + α * (x ^ 2) + (1 : ℂ) * (x ^ 2) ^ 2 = 0 := by
    rw [(by ring : γ + α * (x ^ 2) + (1 : ℂ) * (x ^ 2) ^ 2 = γ + α * x ^ 2 + x ^ 4)]
    apply h
  have hone : (1 : ℂ) ≠ 0 := one_ne_zero
  have hroot := OrEqS_Div.of.Eq0Add_Mul_Square.Ne_0 (x := x ^ 2) hone hy
  have hΔ : (α ^ 2 - 4 * (1 : ℂ) * γ) = Δ := by
    simp [Δ]
  obtain hpos | hneg := hroot
  ·
    rw [hΔ] at hpos
    have hx2 : x ^ 2 = (√Δ - α) / 2 := by
      convert hpos using 1
      ring
    exact Or.inl (Or_Eq_NegSqrt.of.EqSquare hx2)
  ·
    rw [hΔ] at hneg
    have hx2 : x ^ 2 = (-√Δ - α) / 2 := by
      convert hneg using 1
      ring
    exact Or.inr (Or_Eq_NegSqrt.of.EqSquare hx2)


-- created on 2018-11-26
-- updated on 2026-08-30
