import sympy.Basic


@[main]
private lemma main
  [GroupWithZero α]
  [Preorder α]
  {x : α}
-- given
  (h : 1 / x > 0) :
-- imply
  x ≠ 0 := by
-- proof
  contrapose! h
  rw [h]
  simp


-- created on 2025-10-01
