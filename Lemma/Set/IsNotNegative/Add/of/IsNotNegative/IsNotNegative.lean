import sympy.functions.elementary.complexes
import sympy.Basic


@[path]
private lemma main
  {a b : ℂ}
-- given
  (h₀ : a ∈ Complex.ofReal '' Set.Ici 0)
  (h₁ : b ∈ Complex.ofReal '' Set.Ici 0) :
-- imply
  a + b ∈ Complex.ofReal '' Set.Ici 0 := by
-- proof
  obtain ⟨x, hx, rfl⟩ := h₀
  obtain ⟨y, hy, rfl⟩ := h₁
  exact ⟨x + y, Set.mem_Ici.mpr (add_nonneg hx hy), Complex.ofReal_add x y⟩


-- created on 2023-05-03
