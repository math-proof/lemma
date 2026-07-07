import sympy.series.limits
import sympy.Basic


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : x → ∞) :
-- imply
  x ≠ 0 := by
-- proof
  contrapose! h
  subst h
  simp


-- created on 2025-12-17
