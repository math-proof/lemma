import sympy.Basic


@[main]
private lemma main
  [Zero α] [Preorder α]
  {a b : α}
-- given
  (h : a = b)
  (h_b : b > 0) :
-- imply
  a > 0 := by
-- proof
  rw [h]
  exact h_b


-- created on 2018-10-27
-- updated on 2026-08-20
