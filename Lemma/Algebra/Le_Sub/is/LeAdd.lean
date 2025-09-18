import Lemma.Basic


@[main, comm, mp, mpr]
private lemma left
  [AddCommGroup α] [LE α] [AddLeftMono α]
-- given
  (a b c : α) :
-- imply
  b ≤ c - a ↔ a + b ≤ c :=
-- proof
  le_sub_iff_add_le'


@[main, comm, mp, mpr]
private lemma main
  [AddGroup α] [LE α] [AddRightMono α]
-- given
  (a b c : α) :
-- imply
  a ≤ c - b ↔ a + b ≤ c :=
-- proof
  le_sub_iff_add_le


-- created on 2024-11-27
