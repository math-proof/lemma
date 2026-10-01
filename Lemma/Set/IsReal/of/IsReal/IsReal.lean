import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {a b : ℂ}
-- given
  (h₀ : a ∈ Set.range Complex.ofReal)
  (h₁ : b ∈ Set.range Complex.ofReal) :
-- imply
  a * b ∈ Set.range Complex.ofReal := by
-- proof
  obtain ⟨x, rfl⟩ := h₀
  obtain ⟨y, rfl⟩ := h₁
  exact ⟨x * y, Complex.ofReal_mul x y⟩


-- created on 2022-04-03
