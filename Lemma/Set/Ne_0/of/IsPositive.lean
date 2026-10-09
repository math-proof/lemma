import sympy.functions.elementary.complexes
import sympy.Basic


@[path]
private lemma main
  {x : ℂ}
-- given
  (h : x ∈ Complex.ofReal '' Set.Ioi 0) :
-- imply
  x ≠ 0 := by
-- proof
  obtain ⟨r, hr, rfl⟩ := h
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt hr)


-- created on 2023-05-03
