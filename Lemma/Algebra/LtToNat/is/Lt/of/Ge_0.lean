import Lemma.Basic


@[main, comm, mp, mpr]
private lemma main
  {z : ℤ}
-- given
  (h : 0 ≤ z)
  (n : ℕ) :
-- imply
  z.toNat < n ↔ z < n :=
-- proof
  Int.toNat_lt h


-- created on 2025-08-02
