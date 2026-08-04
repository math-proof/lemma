import sympy.Basic


@[main, comm 1]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {x y : α}
-- given
  (h : x ≤ y) :
-- imply
  x - 1 < y := by
-- proof
  have h' := sub_le_sub_right h 1
  exact h'.trans_lt (sub_lt_self y zero_lt_one)


-- created on 2025-03-28
-- updated on 2025-05-03
