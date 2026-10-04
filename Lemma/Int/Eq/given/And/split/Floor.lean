import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
  {y : ℤ}
-- given
  (h : y = ⌊x⌋) :
-- imply
  x - 1 < y ∧ y ≤ x := by
-- proof
  constructor
  ·
    rw [h]
    linarith [Int.lt_floor_add_one x]
  ·
    rw [h]
    exact Int.floor_le x


-- created on 2019-03-29
