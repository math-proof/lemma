import sympy.Basic


@[main]
private lemma main
  {x y : ℤ}
-- given
  (h : x = min x y) :
-- imply
  x ≤ y := by
-- proof
  rw [h]
  exact min_le_right x y


-- created on 2023-03-26
