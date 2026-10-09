import sympy.Basic


@[path]
private lemma main
  {x d : ℝ}
  {k : ℤ}
-- given
  (hd : d ≠ 0) :
-- imply
  ⌊(x + d * k) / d⌋ = ⌊x / d⌋ + k := by
-- proof
  rw [add_div, mul_div_cancel_left₀ _ hd, Int.floor_add_intCast]


-- created on 2018-08-10
