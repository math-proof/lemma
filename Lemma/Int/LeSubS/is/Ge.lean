import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [AddGroup α]
  [LE α]
  [AddLeftMono α]
  [AddRightMono α]
-- given
  (a x y : α) :
-- imply
  a - y ≤ a - x ↔ y ≥ x :=
-- proof
  sub_le_sub_iff_left a


-- created on 2025-09-30
