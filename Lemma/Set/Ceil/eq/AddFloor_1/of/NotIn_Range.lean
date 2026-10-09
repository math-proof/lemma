import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : x ∉ Set.range (Int.cast : ℤ → ℝ)) :
-- imply
  ⌈x⌉ = ⌊x⌋ + 1 := by
-- proof
  exact (Int.ceil_eq_floor_add_one_iff_notMem x).mpr h


-- created on 2018-05-17
