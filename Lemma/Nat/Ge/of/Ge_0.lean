import sympy.Basic


@[main]
private lemma main
  [AddGroup α] [LE α] [AddRightMono α]
  {a b : α}
-- given
  (h : 0 ≤ a - b) :
-- imply
  a ≥ b :=
-- proof
  sub_nonneg.mp h


-- created on 2026-09-26
