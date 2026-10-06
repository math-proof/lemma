import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b w x₀ x₁ : ℝ}
-- given
  (hw : w ∈ Set.Icc 0 1)
  (h₀ : x₀ ∈ Set.Ioc a b)
  (h₁ : x₁ ∈ Set.Ioc a b) :
-- imply
  x₀ * w + x₁ * (1 - w) ∈ Set.Ioc a b := by
-- proof
  obtain ⟨hw0, _⟩ := hw
  obtain ⟨hax0, hx0b⟩ := h₀
  obtain ⟨hax1, hx1b⟩ := h₁
  have h1w : 0 ≤ 1 - w := by linarith
  have hhi : x₀ * w + x₁ * (1 - w) ≤ b := by
    calc
      _ ≤ b * w + b * (1 - w) := add_le_add (mul_le_mul_of_nonneg_right hx0b hw0)
          (mul_le_mul_of_nonneg_right hx1b h1w)
      _ = b := by ring
  have hlo : a < x₀ * w + x₁ * (1 - w) := by
    if h : 0 < w then
      calc
        _ = a * w + a * (1 - w) := by ring
        _ < _ := add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_right hax0 h)
            (mul_le_mul_of_nonneg_right hax1.le h1w)
    else
      have hw0' : w = 0 := by linarith
      rw [hw0']
      simpa using hax1
  exact ⟨hlo, hhi⟩


-- created on 2020-05-30
-- updated on 2023-05-04
