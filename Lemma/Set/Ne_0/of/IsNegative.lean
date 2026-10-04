import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {x : ℂ}
-- given
  (h : x ∈ Complex.ofReal '' Set.Iio 0) :
-- imply
  x ≠ 0 := by
-- proof
  obtain ⟨r, hr, rfl⟩ := h
  exact Complex.ofReal_ne_zero.mpr (ne_of_lt hr)


-- created on 2023-05-03
-- updated on 2025-04-20
