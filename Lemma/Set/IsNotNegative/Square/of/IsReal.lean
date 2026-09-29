import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {x : ℂ}
-- given
  (h : x ∈ Set.range Complex.ofReal) :
-- imply
  x ^ 2 ∈ Complex.ofReal '' Set.Ici 0 := by
-- proof
  obtain ⟨r, rfl⟩ := h
  exact ⟨r ^ 2, sq_nonneg r, Complex.ofReal_pow r 2⟩


-- created on 2026-09-27
