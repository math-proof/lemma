import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main :
-- imply
  ((√3 : ℝ) : ℂ) ^ 2 = 3 := by
-- proof
  rw [← Complex.ofReal_pow]
  simp


-- created on 2026-10-07
