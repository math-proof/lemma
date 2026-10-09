import sympy.Basic


@[path]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {x : α}
  {y : ℤ}
-- given
  (h₀ : x - 1 < y)
  (h₁ : y ≤ x) :
-- imply
  y = ⌊x⌋ := by
-- proof
  rw [eq_comm, Int.floor_eq_iff]
  constructor
  ·
    exact h₁
  ·
    exact sub_lt_iff_lt_add.mp h₀


-- created on 2019-03-08
