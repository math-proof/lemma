import sympy.Basic


@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma main
-- given
  (a b c : ℕ) :
-- imply
  c - b ≤ a ↔ c ≤ a + b :=
-- proof
  Nat.sub_le_iff_le_add


@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma left
-- given
  (a b c : ℕ) :
-- imply
  c - a ≤ b ↔ c ≤ a + b :=
-- proof
  Nat.sub_le_iff_le_add'


-- created on 2024-11-27
-- updated on 2025-10-16
