import sympy.Basic


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {x : α}
  {y : ℤ}
-- given
  (h : x - 1 < y ∧ y ≤ x) :
-- imply
  y = ⌊x⌋ := by
-- proof
  rw [eq_comm, Int.floor_eq_iff]
  constructor
  ·
    exact h.2
  ·
    exact sub_lt_iff_lt_add.mp h.1


-- created on 2019-03-29
