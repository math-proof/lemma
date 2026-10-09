import sympy.Basic


@[path]
private lemma quotient
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {m d q : ℤ}
-- given
  (h : d ≠ 0) :
-- imply
  ⌊(m + d * q) / (d : α)⌋ = ⌊m / (d : α)⌋ + q := by
-- proof
  have hd : (d : α) ≠ 0 := by exact_mod_cast h
  rw [add_div, mul_div_cancel_left₀ _ hd, Int.floor_add_intCast]


-- created on 2018-08-10
