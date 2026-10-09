import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
  {t : ℤ} :
-- imply
  t + ⌈x⌉ = ⌈x + t⌉ := by
-- proof
  rw [Int.ceil_add_intCast, add_comm]


-- created on 2018-11-07
