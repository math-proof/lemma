import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {a b : ℂ}
-- given
  (h₀ : b ∈ Set.range Complex.ofReal)
  (h₁ : a ∈ Complex.ofReal '' Set.Ioi 0) :
-- imply
  b / a ∈ Set.range Complex.ofReal := by
-- proof
  obtain ⟨x, -, rfl⟩ := h₁
  obtain ⟨y, rfl⟩ := h₀
  exact ⟨y / x, Complex.ofReal_div y x⟩


-- created on 2023-05-03
