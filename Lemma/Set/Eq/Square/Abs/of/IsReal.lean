import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {x : ℂ}
-- given
  (h : x ∈ Set.range Complex.ofReal) :
-- imply
  x ^ 2 = (‖x‖ : ℂ) ^ 2 := by
-- proof
  obtain ⟨r, rfl⟩ := h
  rw [Complex.norm_real, Real.norm_eq_abs, ← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs]


-- created on 2023-06-26
