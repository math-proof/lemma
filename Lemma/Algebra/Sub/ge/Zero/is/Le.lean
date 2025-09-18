import Lemma.Basic


@[main, comm, mp, mpr]
private lemma main
  [AddGroup α] [LE α] [AddRightMono α]
  {a b : α} :
-- imply
  b - a ≥ 0 ↔ a ≤ b :=
-- proof
  sub_nonneg


-- created on 2024-11-25
