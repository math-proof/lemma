import sympy.functions.elementary.complexes
import sympy.Basic


@[path]
private lemma main
  {x : ℂ}
-- given
  (h : x ∈ Complex.ofReal '' Set.Ioi 0) :
-- imply
  x ∈ Set.range Complex.ofReal := by
-- proof
  obtain ⟨r, -, rfl⟩ := h
  exact ⟨r, rfl⟩


-- created on 2023-05-03
