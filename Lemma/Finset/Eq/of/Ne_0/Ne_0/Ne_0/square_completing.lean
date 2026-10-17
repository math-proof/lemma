import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import sympy.Basic


@[path]
private lemma main
  {A B x y z : ℝ}
-- given
  (h₀ : A ≠ 0)
  (h₁ : B ≠ 0)
  (h₂ : A + B ≠ 0) :
-- imply
  (x - y) * A * (x - y) + (x - z) * B * (x - z) =
    (x - (A * y + B * z) / (A + B)) * (A + B) *
      (x - (A * y + B * z) / (A + B)) +
    (y - z) * (A⁻¹ + B⁻¹)⁻¹ * (y - z) := by
-- proof
  have hden : A * B ≠ 0 := mul_ne_zero h₀ h₁
  have hsum : A⁻¹ + B⁻¹ = (A + B) / (A * B) := by
    field_simp [h₀, h₁]
    exact add_comm _ _
  have hk : (A⁻¹ + B⁻¹)⁻¹ = A * B / (A + B) := by
    rw [hsum, inv_div]
  rw [hk]
  field_simp [h₀, h₁, h₂, hden]
  ring


-- created on 2023-04-30
-- updated on 2026-10-17
