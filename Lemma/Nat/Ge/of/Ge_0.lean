import sympy.Basic


@[path]
private lemma main
  [AddGroup α] [LE α] [AddRightMono α]
  {a b : α}
-- given
  (h : 0 ≤ a - b) :
-- imply
  a ≥ b :=
-- proof
  sub_nonneg.mp h


@[path]
private lemma scale
  {a t : ℝ}
-- given
  (ht : t ≥ 1)
  (h : a ≥ 0) :
-- imply
  t * a ≥ a := by
-- proof
  nlinarith


-- created on 2019-05-26
-- updated on 2026-09-27
