import sympy.sets.sets
import sympy.core.numbers
import sympy.functions.elementary.trigonometric
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x ∈ Icc 0 1) :
-- imply
  arcsin x ∈ Icc 0 (π / 2) := by
-- proof
  refine ⟨?_, Real.arcsin_le_pi_div_two x⟩
  exact Real.arcsin_nonneg.mpr h.1


-- created on 2026-08-05
