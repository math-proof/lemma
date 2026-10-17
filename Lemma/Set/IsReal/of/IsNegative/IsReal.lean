import sympy.functions.elementary.complexes
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b : ℂ}
-- given
  (h₀ : a ∈ Complex.ofReal '' Set.Iio 0)
  (h₁ : b ∈ Set.range Complex.ofReal) :
-- imply
  b / a ∈ Set.range Complex.ofReal := by
-- proof
  obtain ⟨x, hx, rfl⟩ := h₀
  obtain ⟨y, rfl⟩ := h₁
  have hx0 : x ≠ 0 := by
    rw [Set.mem_Iio] at hx
    linarith
  exact ⟨y / x, Complex.ofReal_div y x⟩


-- created on 2026-10-11
-- updated on 2026-10-17
