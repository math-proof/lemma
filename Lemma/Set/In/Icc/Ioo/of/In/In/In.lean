import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b w x₀ x₁ : ℝ}
-- given
  (hw : w ∈ Set.Ioo 0 1)
  (h₀ : x₀ ∈ Set.Ioc a b)
  (h₁ : x₁ ∈ Set.Ioc a b) :
-- imply
  x₀ * w + x₁ * (1 - w) ∈ Set.Ioc a b := by
-- proof
  obtain ⟨hw0, _⟩ := hw
  obtain ⟨hax0, hx0b⟩ := h₀
  obtain ⟨hax1, hx1b⟩ := h₁
  have hp : 0 < 1 - w := by linarith
  have hlo : a < x₀ * w + x₁ * (1 - w) := by
    calc
      _ = a * w + a * (1 - w) := by ring
      _ < _ := add_lt_add (mul_lt_mul_of_pos_right hax0 hw0)
          (mul_lt_mul_of_pos_right hax1 hp)
  have hhi : x₀ * w + x₁ * (1 - w) ≤ b := by
    calc
      _ ≤ b * w + b * (1 - w) := add_le_add (mul_le_mul_of_nonneg_right hx0b hw0.le)
          (mul_le_mul_of_nonneg_right hx1b hp.le)
      _ = b := by ring
  exact ⟨hlo, hhi⟩


-- created on 2020-05-08
