import Lemma.Basic


@[main, comm, mp, mpr]
private lemma nat
-- given
  (a b c : ℕ) :
-- imply
  c - b ≤ a ↔ c ≤ a + b :=
-- proof
  Nat.sub_le_iff_le_add


@[main, comm, mp, mpr]
private lemma left.nat
-- given
  (a b c : ℕ) :
-- imply
  c - a ≤ b ↔ c ≤ a + b :=
-- proof
  Nat.sub_le_iff_le_add'


@[main, comm, mp, mpr]
private lemma left
  [AddCommGroup α] [LE α] [AddLeftMono α]
-- given
  (a b c : α) :
-- imply
  c - a ≤ b ↔ c ≤ a + b :=
-- proof
  sub_le_iff_le_add'


@[main, comm, mp, mpr]
private lemma main
  [AddGroup α] [LE α] [AddRightMono α]
-- given
  (a b c : α) :
-- imply
  c - b ≤ a ↔ c ≤ a + b :=
-- proof
  sub_le_iff_le_add


-- created on 2024-11-27
-- updated on 2025-05-09
