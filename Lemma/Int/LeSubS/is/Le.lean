import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [AddGroup α]
  [LE α]
  [AddRightMono α]
-- given
  (x y c : α) :
-- imply
  x - c ≤ y - c ↔ x ≤ y :=
-- proof
  sub_le_sub_iff_right c


-- created on 2025-05-14
-- updated on 2025-09-30
