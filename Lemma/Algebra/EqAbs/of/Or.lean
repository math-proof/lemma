import sympy.Basic


@[main]
private lemma main
  [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  {x y : α}
-- given
  (h : y = x ∨ y = -x) :
-- imply
  |y| = |x| := by
-- proof
  rcases h with h | h
  ·
    rw [h]
  ·
    rw [h, abs_neg]


-- created on 2018-08-14
-- updated on 2026-08-20
