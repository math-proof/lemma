import Lemma.Basic


@[main, comm, mp, mpr]
private lemma main
  {b c : ℕ}
-- given
  (h : b ≤ c)
  (a : ℕ) :
-- imply
  a ≤ c - b ↔ a + b ≤ c :=
-- proof
  Nat.le_sub_iff_add_le h


@[main, comm, mp, mpr]
private lemma left
  {a c : ℕ}
-- given
  (h : a ≤ c)
  (b : ℕ):
-- imply
  b ≤ c - a ↔ a + b ≤ c :=
-- proof
  Nat.le_sub_iff_add_le' h


-- created on 2025-06-21
