import sympy.Basic


@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma left
  [AddCommGroup α] [LE α] [AddLeftMono α]
-- given
  (a b c : α) :
-- imply
  c - a ≤ b ↔ c ≤ a + b :=
-- proof
  sub_le_iff_le_add'


@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma main
  [AddGroup α] [LE α] [AddRightMono α]
-- given
  (a b c : α) :
-- imply
  c - b ≤ a ↔ c ≤ a + b :=
-- proof
  sub_le_iff_le_add


-- created on 2025-10-16
