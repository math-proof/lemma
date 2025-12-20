import sympy.Basic


@[main]
private lemma left
  [PartialOrder α] [MulZeroClass α]
  {a b : α}
-- given
  (h : a * b > 0) :
-- imply
  a ≠ 0 := by
-- proof
  by_contra h'
  rw [h'] at h
  simp at h


@[main]
private lemma main
  [PartialOrder α] [MulZeroClass α]
  {a b : α}
-- given
  (h : a * b > 0) :
-- imply
  b ≠ 0 := by
-- proof
  by_contra h'
  rw [h'] at h
  simp at h


-- created on 2024-11-30
-- updated on 2025-06-13
