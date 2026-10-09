import sympy.Basic


@[path]
private lemma main
  [AddGroup α] [LE α] [AddRightMono α]
  {x y : α}
-- given
  (h : x ≤ y) :
-- imply
  y - x ≥ 0 :=
-- proof
  sub_nonneg.mpr h


@[path]
private lemma given
  [AddGroup α] [LE α] [AddRightMono α]
  {a b : α}
-- given
  (h : b ≤ a) :
-- imply
  0 ≤ a - b :=
-- proof
  sub_nonneg.mpr h


-- created on 2023-04-15
