import sympy.functions.elementary.complexes
import sympy.Basic


@[path]
private lemma transplant
  {x y d : ℝ}
-- given
  (h : x * y = d)
  (_h : d ≠ 0) :
-- imply
  x * y / x = d / x := by
-- proof
  rw [h]


-- created on 2021-11-09
