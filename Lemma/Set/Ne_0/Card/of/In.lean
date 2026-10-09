import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : x ∈ (Set.univ : Set ℝ) \ {0}) :
-- imply
  |x| ≠ 0 := by
-- proof
  apply abs_ne_zero.mpr
  intro hx
  exact h.2 (Set.mem_singleton_iff.mpr hx)


-- created on 2021-03-13
