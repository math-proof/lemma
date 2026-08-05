import sympy.sets.sets
import sympy.functions.elementary.trigonometric
import sympy.Basic
open Set Real


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x ∈ Icc 0 1) :
-- imply
  arcsin x ∈ Icc 0 (Real.pi / 2) := by
-- proof
  refine ⟨?_, arcsin_le_pi_div_two x⟩
  exact arcsin_nonneg.mpr h.1


-- created on 2026-08-05
