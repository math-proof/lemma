import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {a b : ℂ}
-- given
  (h₀ : a ∈ Complex.ofReal '' Set.Ioi 0)
  (h₁ : b ∈ Set.range Complex.ofReal) :
-- imply
  b / a ∈ Set.range Complex.ofReal := by
-- proof
  obtain ⟨x, -, rfl⟩ := h₀
  obtain ⟨y, rfl⟩ := h₁
  exact ⟨y / x, Complex.ofReal_div y x⟩


-- created on 2023-05-03
